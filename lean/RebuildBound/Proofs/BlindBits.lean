import RebuildBound.Proofs.BlindBits.Bits
import RebuildBound.Proofs.BlindBits.Route
import RebuildBound.Proofs.BlindBits.Blind
import RebuildBound.Proofs.BlindBits.Words

/-!
# BlindBits: bit words, key sets and flattened routes

`natToBits`/`clrBit`/`dN` and the bit-word equivalences (`BlindBits.Bits`, from
`G2/Bits`), `flat` (`BlindBits.Route`, from `G2/Route`), `keysOf`/`wOf`
(`BlindBits.Blind`, from `G2/Blind`), `avg_comp` and `inRange_natToBits`
(`BlindBits.Words`, from `G2/Words`, `G2/Range`). Used by G2, SG2, TG1, TG2,
G3 and DirectJobUniform. Namespace `RebuildBound.G2` kept.
-/
