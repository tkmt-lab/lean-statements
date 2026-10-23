# Correspondence with the published statements

Each file is an independent Lean module. Removing the documented metadata additions
reconstructs the original published source bytes. `tools/check.py --static-only` checks
the hashes in [manifest.json](manifest.json). The original definitions, namespaces,
hypotheses and intentional `sorry` bodies are retained.

| File | Source commit | Theorems |
|---|---|---:|
| [A3](FormalConjectures/Paper/A3.lean) | [tkmt-lab/a3-gsw-classification / 58124b20fa4a](https://github.com/tkmt-lab/a3-gsw-classification/blob/58124b20fa4a3b19aaa62e734c2036210f7bdcf8/packet/formal/Formal/ComparatorChallengeMain.lean) | 1 |
| [AffineRays](FormalConjectures/Paper/AffineRays.lean) | [tkmt-lab/gsw-ray-periodicity / 8a53918db58f](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/Challenge2.lean) | 1 |
| [K3](FormalConjectures/Paper/K3.lean) | [tkmt-lab/gsw-ray-periodicity / 8a53918db58f](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeK3.lean) | 1 |
| [C1](FormalConjectures/Paper/C1.lean) | [tkmt-lab/gsw-ray-periodicity / 8a53918db58f](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeC1.lean) | 2 |
| [O2](FormalConjectures/Paper/O2.lean) | [tkmt-lab/gsw-ray-periodicity / 8a53918db58f](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeO2.lean) | 2 |
| [D14](FormalConjectures/Paper/D14.lean) | [tkmt-lab/gsw-ray-periodicity / 8a53918db58f](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeD14.lean) | 1 |
| [E10](FormalConjectures/Paper/E10.lean) | [tkmt-lab/gsw-ray-periodicity / 8a53918db58f](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeE10.lean) | 2 |
| [Heesch](FormalConjectures/Paper/Heesch.lean) | [tkmt-lab/heesch-certificates / 271bc8ce223a](https://github.com/tkmt-lab/heesch-certificates/blob/271bc8ce223a1fd641494352eb31f350e3d8bf37/formal/Heesch/Challenge.lean) | 6 |
| [D12](FormalConjectures/Paper/D12.lean) | [tkmt-lab/gsw-ray-periodicity / 8eea5994bfeb](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8eea5994bfebdcca4865528bd7524af4064f9c16/statement/ChallengeD12.lean) | 2 |

## Declaration mapping

The digest is SHA-256 of the serialized Lean expression for the theorem type,
equal in the original and normalized environments at the toolchain pinned here.

| File | Declaration | Source / local line | Public proof | Type digest (prefix) |
|---|---|---|---|---|
| A3 | `ClaudeChallenge.main` | 129 / 175 | [proof](https://github.com/tkmt-lab/a3-gsw-classification/blob/58124b20fa4a3b19aaa62e734c2036210f7bdcf8/packet/formal/Formal/ComparatorSolutionMain.lean#L7) | `74fd43df5999ec50` |
| AffineRays | `ClaudeChallenge2.main` | 169 / 215 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude3ComparatorSolution.lean#L10) | `efdfae0d29d5b804` |
| K3 | `ClaudeChallengeK3.main` | 166 / 212 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude4K3ComparatorSolution.lean#L23) | `ae2509325e3a3a83` |
| C1 | `ClaudeChallengeC1.classification` | 152 / 198 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude4C1ComparatorSolution.lean#L24) | `a98429f54619a0b5` |
| C1 | `ClaudeChallengeC1.main` | 157 / 205 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude4C1ComparatorSolution.lean#L29) | `312e45cf79801d2c` |
| O2 | `ClaudeChallengeO2.classification` | 164 / 210 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5O2ComparatorSolution.lean#L27) | `fb7137ed5d0febcc` |
| O2 | `ClaudeChallengeO2.main` | 169 / 217 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5O2ComparatorSolution.lean#L32) | `b34cd3796fb6b9e7` |
| D14 | `ClaudeChallengeD14.main` | 164 / 210 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5D14ComparatorSolution.lean#L29) | `7f3039ef0c760cdc` |
| E10 | `ClaudeChallengeE10.classification` | 208 / 254 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5E10ComparatorSolution.lean#L31) | `290949d2de486313` |
| E10 | `ClaudeChallengeE10.main` | 216 / 264 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5E10ComparatorSolution.lean#L40) | `71cd35e54012aea5` |
| Heesch | `Heesch.hh_sound_square` | 523 / 568 | [proof](https://github.com/tkmt-lab/heesch-certificates/blob/271bc8ce223a1fd641494352eb31f350e3d8bf37/formal/Heesch/Solution.lean#L21) | `656a5907b5eaf7e1` |
| Heesch | `Heesch.hc_sound_square` | 531 / 578 | [proof](https://github.com/tkmt-lab/heesch-certificates/blob/271bc8ce223a1fd641494352eb31f350e3d8bf37/formal/Heesch/Solution.lean#L29) | `dcb12975f92b3827` |
| Heesch | `Heesch.hh_sound_hex` | 539 / 588 | [proof](https://github.com/tkmt-lab/heesch-certificates/blob/271bc8ce223a1fd641494352eb31f350e3d8bf37/formal/Heesch/Solution.lean#L37) | `f34d288b1ef4642b` |
| Heesch | `Heesch.hc_sound_hex` | 547 / 598 | [proof](https://github.com/tkmt-lab/heesch-certificates/blob/271bc8ce223a1fd641494352eb31f350e3d8bf37/formal/Heesch/Solution.lean#L45) | `bab6eeaa7c040095` |
| Heesch | `Heesch.hh_sound_tri` | 555 / 608 | [proof](https://github.com/tkmt-lab/heesch-certificates/blob/271bc8ce223a1fd641494352eb31f350e3d8bf37/formal/Heesch/Solution.lean#L53) | `7bcc7e68a42f49e2` |
| Heesch | `Heesch.hc_sound_tri` | 563 / 618 | [proof](https://github.com/tkmt-lab/heesch-certificates/blob/271bc8ce223a1fd641494352eb31f350e3d8bf37/formal/Heesch/Solution.lean#L61) | `8b68874aea4643be` |
| D12 | `ClaudeChallengeD12.classification` | 165 / 212 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8eea5994bfebdcca4865528bd7524af4064f9c16/packet/formal/Formal/Claude7D12ComparatorSolution.lean#L32) | `1f238a5f03c50ec2` |
| D12 | `ClaudeChallengeD12.main` | 172 / 221 | [proof](https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8eea5994bfebdcca4865528bd7524af4064f9c16/packet/formal/Formal/Claude7D12ComparatorSolution.lean#L39) | `48edb1aeb0784bf5` |

## Checks and limits

The [recorded summary](checks/statement-correspondence.json) covers all 18 theorem
type pairs and the parsed solved/proof-link attributes. The definitions are protected
by exact reconstruction of the original source bytes. The check uses Lean 4.35.0 and
Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The mathematical proof closures were not executed by these packaging checks. The
general affine-ray statement retains its explicit formal hypotheses and its source
paper’s prose correspondence boundary. E10 classification requires r ≥ 2; its ray
theorem includes r = 1. D12 classification includes r,s ≥ 1. Heesch statements retain
all counter-order, layer, hole-validity and unsatisfiability hypotheses.

`tools/check.py` can reproduce the original/normalized comparison from this package’s
local dependency cache. Generated logs may contain the user’s local paths and stay in
ignored work folders. The public summary omits commands, internal identifiers and local paths.

Lean 4.33.1 and the complete formal-conjectures linter suite have not been checked.
