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

    const C = opt.C[t - 2];
    const S = opt.S[t - 2];
    const M = opt.M[t - 2];
    const P = opt.P[t - 2];

    const contract = new Contract();

    function saveM() {
        for (let i=0; i<t; i++) {
            for (let j=0; j<t; j++) {
                contract.push(toHex256(M[t-2][i][j])); // val
                contract.push((1+i*t+j)*32); // address, val
                contract.mstore(); //
            }
        }
    }

    function ark(r) {   // st, q
        for (let i=0; i<t; i++) {
            contract.dup(t); // q, st, q
            contract.push(toHex256(C[r*t+i]));  // K, q, st, q
            contract.dup(2+i); // st[i], K, q, st, q
            contract.addmod(); // newSt[i], st, q
            contract.swap(1 + i); // xx, st, q
            contract.pop();
        }
    }

    function sigma(p) {
        // sq, q
        contract.dup(t);   // q, st, q
        contract.dup(1+p); // st[p] , q , st, q
        contract.dup(1);   // q, st[p] , q , st, q
        contract.dup(0);   // q, q, st[p] , q , st, q
        contract.dup(2);   // st[p] , q, q, st[p] , q , st, q
        contract.dup(0);   // st[p] , st[p] , q, q, st[p] , q , st, q
        contract.mulmod(); // st2[p], q, st[p] , q , st, q
        contract.dup(0);   // st2[p], st2[p], q, st[p] , q , st, q
        contract.mulmod(); // st4[p], st[p] , q , st, q
        contract.mulmod(); // st5[p], st, q
        contract.swap(1+p);
        contract.pop();      // newst, q
    }

    function mix() {
        contract.label("mix");
        for (let i=0; i<t; i++) {
            for (let j=0; j<t; j++) {
                if (j==0) {
                    contract.dup(i+t);      // q, newSt, oldSt, q
                    contract.push((1+i*t+j)*32);
                    contract.mload();      // M, q, newSt, oldSt, q
                    contract.dup(2+i+j);    // oldSt[j], M, q, newSt, oldSt, q
                    contract.mulmod();      // acc, newSt, oldSt, q
                } else {
                    contract.dup(1+i+t);    // q, acc, newSt, oldSt, q
                    contract.push((1+i*t+j)*32);
                    contract.mload();      // m[i, j], q, acc, newSt, oldSt, q
                    contract.dup(3+i+j);    // oldSt[j], M, q, acc, newSt, oldSt, q
                    contract.mulmod();      // aux, acc, newSt, oldSt, q
                    contract.dup(2+i+t);    // q, aux, acc, newSt, oldSt, q
                    contract.swap(2);       // acc, aux, q, newSt, oldSt, q
                    contract.addmod();      // acc, newSt, oldSt, q
                }
            }
        }
        for (let i=0; i<t; i++) {
            contract.swap((t -i) + (t -i-1));
            contract.pop();
        }
        contract.push(0);
        contract.mload(); //label
        contract.jmp();
    }


    // Check selector
    contract.push("0x0100000000000000000000000000000000000000000000000000000000");
    contract.push(0);
    contract.calldataload();
    contract.div();
    contract.dup(0);
    contract.push(ethers.utils.keccak256(ethers.utils.toUtf8Bytes(`poseidon(uint256[${nInputs}])`)).slice(0, 10)); // poseidon(uint256[n])
    contract.eq();
    contract.swap(1);
    contract.push(ethers.utils.keccak256(ethers.utils.toUtf8Bytes(`poseidon(bytes32[${nInputs}])`)).slice(0, 10)); // poseidon(bytes32[n])
    contract.eq();
    contract.or();
    contract.jmpi("start");
    contract.invalid();

    contract.label("start");

    saveM();

    contract.push("0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001");  // q

    // Load t values from the call data.
    // The function has a single array param param
    // [Selector (4)] [item1 (32)] [item2 (32)] ....
    // Stack positions 0-nInputs.
    for (let i=0; i<nInputs; i++) {
        contract.push(0x04+(0x20*(nInputs-i-1)));
        contract.calldataload();
    }

    contract.push(0);

    ark(0);
    // state = state.map((a, i) => F.add(a, C[i]));
    for (let r = 0; r < nRoundsF/2-1; r++) {
        for (let j=0; j<t; j++) {
            sigma(j);
        }
        ark(r+1);

        const strLabel = "aferMix"+r;
        contract._pushLabel(strLabel);
        contract.push(0);
        contract.mstore();
        contract.jmp("mix");
        contract.label(strLabel);

    }

    for (let j=0; j<t; j++) {
        sigma(j);
        ark(nRoundsF/2)
    }

    const strLabel = "aferMix_full";
    contract._pushLabel(strLabel);
    contract.push(0);
    contract.mstore();
    contract.jmp("mix");
    contract.label(strLabel);



    // for (let r = 0; r < nRoundsP; r++) {
    //     state[0] = pow5(state[0]);
    //     state[0] = F.add(state[0], C[(nRoundsF/2 +1)*t + r]);
    //
    //
    //     const s0 = state.reduce((acc, a, j) => {
    //         return F.add(acc, F.mul(S[(t*2-1)*r+j], a));
    //     }, F.zero);
    //     for (let k=1; k<t; k++) {
    //         state[k] = F.add(state[k], F.mul(state[0], S[(t*2-1)*r+t+k-1]   ));
    //     }
    //     state[0] =s0;
    // }


    // Old
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
        contract._pushLabel(strLabel);
        contract.push(0);
        contract.mstore();
        contract.jmp("mix");
        contract.label(strLabel);
    }

    contract.push("0x00");
    contract.mstore();     // Save it to pos 0;
    contract.push("0x20");
    contract.push("0x00");
    contract.return();

    mix();

    return contract.createTxData();
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



