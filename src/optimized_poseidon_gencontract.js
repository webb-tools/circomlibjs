// Copyright (c) 2018 Jordi Baylina
// License: LGPL-3.0+
//

import Contract from "./evmasm.js";
import { utils } from "ffjavascript";
const { unstringifyBigInts } = utils;
import ethers from "ethers";

import poseidonConstants from "./poseidon_constants_opt.js";

const opt = unstringifyBigInts(poseidonConstants);


const N_ROUNDS_F = 8;
const N_ROUNDS_P = [56, 57, 56, 60, 60, 63, 64, 63];

function toHex256(a) {
    let S = a.toString(16);
    while (S.length < 64) S="0"+S;
    return "0x" + S;
}

export function createCode(nInputs) {

    if (( nInputs<1) || (nInputs>8)) throw new Error("Invalid number of inputs. Must be 1<=nInputs<=8");
    const t = nInputs + 1;
    const nRoundsF = N_ROUNDS_F;
    const nRoundsP = N_ROUNDS_P[t - 2];

    const K = opt.C[t - 2];
    // K in assembly = C in javascript !!
    const S = opt.S[t - 2];
    const M = opt.M[t - 2];
    const P = opt.P[t - 2];

    const C = new Contract();

    function saveM() {
        for (let i=0; i<t; i++) {
            for (let j=0; j<t; j++) {
                C.push(toHex256(M[i][j])); // val
                C.push((1+i*t+j)*32); // address, val
                C.mstore(); //
            }
        }
    }
    function saveP() {
        for (let i=t; i<2*t; i++) {
            for (let j=t; j<2*t; j++) {
                C.push(toHex256(P[i][j])); // val
                C.push((1+i*t+j)*32); // address, val
                C.mstore(); //
            }
        }
    }

    function ark(r) {   // st, q
        for (let i=0; i<t; i++) {
            C.dup(t); // q, st, q
            // K in assembly = C in javascript !!
            C.push(toHex256(K[r*t+i]));  // K, q, st, q
            C.dup(2+i); // st[i], K, q, st, q
            C.addmod(); // newSt[i], st, q
            C.swap(1 + i); // xx, st, q
            C.pop();
        }
    }

    function sigma(p) {
        // sq, q
        C.dup(t);   // q, st, q
        C.dup(1+p); // st[p] , q , st, q
        C.dup(1);   // q, st[p] , q , st, q
        C.dup(0);   // q, q, st[p] , q , st, q
        C.dup(2);   // st[p] , q, q, st[p] , q , st, q
        C.dup(0);   // st[p] , st[p] , q, q, st[p] , q , st, q
        C.mulmod(); // st2[p], q, st[p] , q , st, q
        C.dup(0);   // st2[p], st2[p], q, st[p] , q , st, q
        C.mulmod(); // st4[p], st[p] , q , st, q
        C.mulmod(); // st5[p], st, q
        C.swap(1+p);
        C.pop();      // newst, q
    }

    function pix() { // matrix multiplication per P
        C.label("pix");
        for (let i=0; i<t; i++) {
            for (let j=0; j<t; j++) {
                if (j==0) {
                    C.dup(i+t);      // q, newSt, oldSt, q
                    C.push((1+(i+t)*t+(j+t))*32);
                    C.mload();      // M, q, newSt, oldSt, q
                    C.dup(2+i+j);    // oldSt[j], M, q, newSt, oldSt, q
                    C.mulmod();      // acc, newSt, oldSt, q
                } else {
                    C.dup(1+i+t);    // q, acc, newSt, oldSt, q
                    C.push((1+(i+t)*t+(j+t))*32);
                    C.mload();      // m[i, j], q, acc, newSt, oldSt, q
                    C.dup(3+i+j);    // oldSt[j], M, q, acc, newSt, oldSt, q
                    C.mulmod();      // aux, acc, newSt, oldSt, q
                    C.dup(2+i+t);    // q, aux, acc, newSt, oldSt, q
                    C.swap(2);       // acc, aux, q, newSt, oldSt, q
                    C.addmod();      // acc, newSt, oldSt, q
                }
            }
        }
        for (let i=0; i<t; i++) {
            C.swap((t -i) + (t -i-1));
            C.pop();
        }
        C.push(0);
        C.mload(); //label
        C.jmp();
    }

    function mix() { // matrix multiplication per M
        C.label("mix");
        for (let i=0; i<t; i++) {
            for (let j=0; j<t; j++) {
                if (j==0) {
                    C.dup(i+t);      // q, newSt, oldSt, q
                    C.push((1+i*t+j)*32);
                    C.mload();      // M, q, newSt, oldSt, q
                    C.dup(2+i+j);    // oldSt[j], M, q, newSt, oldSt, q
                    C.mulmod();      // acc, newSt, oldSt, q
                } else {
                    C.dup(1+i+t);    // q, acc, newSt, oldSt, q
                    C.push((1+i*t+j)*32);
                    C.mload();      // m[i, j], q, acc, newSt, oldSt, q
                    C.dup(3+i+j);    // oldSt[j], M, q, acc, newSt, oldSt, q
                    C.mulmod();      // aux, acc, newSt, oldSt, q
                    C.dup(2+i+t);    // q, aux, acc, newSt, oldSt, q
                    C.swap(2);       // acc, aux, q, newSt, oldSt, q
                    C.addmod();      // acc, newSt, oldSt, q
                }
            }
        }
        for (let i=0; i<t; i++) {
            C.swap((t -i) + (t -i-1));
            C.pop();
        }
        C.push(0);
        C.mload(); //label
        C.jmp();
    }

    // Check selector
    C.push("0x0100000000000000000000000000000000000000000000000000000000");
    C.push(0);
    C.calldataload();
    C.div();
    C.dup(0);
    C.push(ethers.utils.keccak256(ethers.utils.toUtf8Bytes(`poseidon(uint256[${nInputs}])`)).slice(0, 10)); // poseidon(uint256[n])
    C.eq();
    C.swap(1);
    C.push(ethers.utils.keccak256(ethers.utils.toUtf8Bytes(`poseidon(bytes32[${nInputs}])`)).slice(0, 10)); // poseidon(bytes32[n])
    C.eq();
    C.or();
    C.jmpi("start");
    C.invalid();

    C.label("start");

    saveM();
    saveP();

    C.push("0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001");  // q

    // Load t values from the call data.
    // The function has a single array param param
    // [Selector (4)] [item1 (32)] [item2 (32)] ....
    // Stack positions 0-nInputs.
    for (let i=0; i<nInputs; i++) {
        C.push(0x04+(0x20*(nInputs-i-1)));
        C.calldataload();
    }

    C.push(0);

    // Begin first full rounds
    ark(0);
    // state = state.map((a, i) => F.add(a, C[i]));
    for (let r = 0; r < nRoundsF/2-1; r++) {
        for (let j=0; j<t; j++) {
            sigma(j);
        }
        ark(r+1);

        const strLabel = "aferMix"+r;
        C._pushLabel(strLabel);
        C.push(0);
        C.mstore();
        C.jmp("mix"); // multiply per M
        C.label(strLabel);
    }

    // another full round with modifications
    for (let j=0; j<t; j++) {
        sigma(j);
    }
    ark(nRoundsF/2) // matches below?: 

    const strLabel = "after_pix";
    C._pushLabel(strLabel);
    C.push(0);
    C.mstore();
    C.jmp("pix"); // multiply per P
    C.label(strLabel);
    // another full round should match implementation below 
    // state = state.map(a => pow5(a));
    // state = state.map((a, i) => F.add(a, C[(nRoundsF/2-1 +1)* t +i]));
    // state = state.map((_, i) =>
    //     state.reduce((acc, a, j) => F.add(acc, F.mul(P[j][i], a)), F.zero)
    // );

    // Begin partial rounds
    for (let r = 0; r < nRoundsP; r++) {
        sigma(0); // sq, q

        // begin state[0] = F.add(state[0], C[(nRoundsF/2 +1)*t + r])
        C.dup(t);  // q, sq, q
        // K in assembly = C in javascript !!
        C.push(toHex256(K[(nRoundsF/2+1)*t+r]));  // K, q, st, q
        C.dup(2); // st[0], K, q, st, q
        C.addmod(); // aux, st, q
        C.swap(1); // xx, st, q
        C.pop(); // st, q

        
        // begin
        // const s0 = state.reduce((acc, a, j) => {
        //     let val = F.add(acc, F.mul(S[(t*2-1)*r+j], a));
        //     console.log("hey:)
        //     return val
        // }, F.zero);
        for(let i = 0; i < t; i++) {
            if (i == 0) {
                C.dup(t); // q, st, q
                C.push(toHex256(S[(t*2 - 1)*r + i])); // S[i], q, st, q
                C.dup(2+i); // st[i], S[i] q, st, q
                C.mulmod(); // acc, st, q
            } else {
                C.dup(t+1); // q, acc, st, q
                C.push(toHex256(S[(t*2-1)*r + i])); // S[i], q, acc, st, q 
                C.dup(2+i); // st[i], S[i] q, acc, st, q
                C.mulmod(); // aux, acc, st, q
                C.dup(2+i+t); // q, aux, acc, st, q
                C.swap(2); // acc, aux, q, st, q
                C.addmod(); // acc, st, q
            }
        }
        //
        // should be right until here
        

        // begin
        // for (let k=1; k<t; k++) {
        //     state[k] = F.add(state[k], F.mul(state[0], S[(t*2-1)*r+t+k-1]));
        // }
        for(let k = 1; k < t; k++) {
            C.dup(t+1); // q, newSt0 st, q
            C.dup(0); // q, q, newSt0, st, q
            C.push(toHex256(S[(t*2-1)*r+t+k-1])); // S, q, q, newSt0 st, q
            C.dup(4); // st[0], S, q, q, newSt0, st, q
            C.mulmod(); // aux, q, newSt0, st, q
            C.dup(3+k); // st[k], S, q, newSt0, st, q
            C.addmod(); // newSt, newSt0, st, q
            C.swap(2+k); // xx, newSt0, st, q
            C.pop(); // newSt0, st, q
        }

        // begin
        // state[0] =s0;
        C.swap(1); // xx, st, q
        C.pop(); // st, q
    }

    // Begin
//state = state.map((a, i) => F.add(a, C[ (nRoundsF/2 +1)*t + nRoundsP + r*t + i ]));
//state = state.map((a, i) => F.add(a, C[(r + 1)* t +i]));
    //     state = state.map((_, i) =>
    //         state.reduce((acc, a, j) => F.add(acc, F.mul(M[j][i], a)), F.zero)
    //     );
    // }
    // }

    // Begin final rounds
    // K in assembly = C in javascript !!
    for(let r = 0; r < nRoundsF/2-1; r++) {
        for (let i=0; i<t; i++) {
            // Begin map[i]
            // state = state.map(a => pow5(a));
            sigma(i); // st, q


            // Begin map[i]
        // state.map((a, i) => F.add(a, C[(nRoundsF/2 +1)*t + nRoundsP + r*t + i ]));
            C.dup(t); // q, st, q
            C.push(toHex256(K[(nRoundsF/2+1)*t + nRoundsP + r*t + i]));  // K, q, st, q
            C.dup(2+i); // st[i], K, q, st, q
            C.addmod(); // newSt[i], st, q
            C.swap(1 + i); // xx, st, q
            C.pop(); // st, q
        }
        // Begin
        // state = state.map((_, i) =>
        //     state.reduce((acc, a, j) => F.add(acc, F.mul(M[j][i], a)), F.zero)
        // );
        const strLabel = "aferMix"+nRoundsF/2+nRoundsP+r;
        C._pushLabel(strLabel);
        C.push(0);
        C.mstore();
        C.jmp("mix"); // multiply by M
        C.label(strLabel);
    }
    // Begin
    // state = state.map(a => pow5(a));
    // state = state.map((_, i) =>
    //     state.reduce((acc, a, j) => F.add(acc, F.mul(M[j][i], a)), F.zero)
    // );
    //
    // return state[0];
    for(let i = 0; i < t; i++) {
        sigma(i); // st, q
    }
    const strLabel = "aferMix_final";
    C._pushLabel(strLabel);
    C.push(0);
    C.mstore();
    C.jmp("mix"); // multiply by M
    C.label(strLabel);

    C.push("0x00");
    C.mstore();     // Save it to pos 0;
    C.push("0x20");
    C.push("0x00");
    C.return();
    for (let i=0; i<nRoundsF+nRoundsP; i++) {
        ark(i);
        // state = state.map((a, i) => F.add(a, C[t - 2][r * t + i]));
        if ((i<nRoundsF/2) || (i>=nRoundsP+nRoundsF/2)) {
            for (let j=0; j<t; j++) {
                sigma(j);
            }
        } else {
            sigma(0);
        }
        const strLabel = "aferMix"+i;
        C._pushLabel(strLabel);
        C.push(0);
        C.mstore();
        C.jmp("mix");
        C.label(strLabel);
    }

    C.push("0x00");
    C.mstore();     // Save it to pos 0;
    C.push("0x20");
    C.push("0x00");
    C.return();

    mix();

    return C.createTxData();
}
}

export function generateABI(nInputs) {
    return [
        {
            "constant": true,
            "inputs": [
                {
                    "internalType": `bytes32[${nInputs}]`,
                    "name": "input",
                    "type": `bytes32[${nInputs}]`
                }
            ],
            "name": "poseidon",
            "outputs": [
                {
                    "internalType": "bytes32",
                    "name": "",
                    "type": "bytes32"
                }
            ],
            "payable": false,
            "stateMutability": "pure",
            "type": "function"
        },
        {
            "constant": true,
            "inputs": [
                {
                    "internalType": `uint256[${nInputs}]`,
                    "name": "input",
                    "type": `uint256[${nInputs}]`
                }
            ],
            "name": "poseidon",
            "outputs": [
                {
                    "internalType": "uint256",
                    "name": "",
                    "type": "uint256"
                }
            ],
            "payable": false,
            "stateMutability": "pure",
            "type": "function"
        }
    ];
}



