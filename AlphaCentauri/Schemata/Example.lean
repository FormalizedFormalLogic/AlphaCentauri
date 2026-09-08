module

public import AlphaCentauri.Schemata.CollectionEquivalence
public import AlphaCentauri.Schemata.CollectionInduction
public import AlphaCentauri.Schemata.LeastNumber

/-!
# Instances of the fragment hierarchy

The relations between the fragments are stated for every index, which leaves the theory zoo — whose
vertices are closed theories — with nothing to draw. These are their instances at the first few
indices.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

theorem BSigma_one_weakerThan_ISigma_one : 𝗕𝚺 1 ⪯ 𝗜𝚺 1 := BSigma_weakerThan_ISigma 0

theorem BSigma_two_weakerThan_ISigma_two : 𝗕𝚺 2 ⪯ 𝗜𝚺 2 := BSigma_weakerThan_ISigma 1

theorem BSigma_one_equiv_BPi_zero : 𝗕𝚺 1 ≊ 𝗕𝚷 0 := BSigma_succ_equiv_BPi 0

theorem BSigma_two_equiv_BPi_one : 𝗕𝚺 2 ≊ 𝗕𝚷 1 := BSigma_succ_equiv_BPi 1

theorem ISigma_one_equiv_IPi_one : 𝗜𝚺 1 ≊ 𝗜𝚷 1 := ISigma_equiv_IPi 1

theorem ISigma_two_equiv_IPi_two : 𝗜𝚺 2 ≊ 𝗜𝚷 2 := ISigma_equiv_IPi 2

theorem LSigma_one_equiv_ISigma_one : 𝗟𝚺 1 ≊ 𝗜𝚺 1 := LSigma_equiv_ISigma 1

theorem LPi_one_equiv_ISigma_one : 𝗟𝚷 1 ≊ 𝗜𝚺 1 := LPi_equiv_ISigma 1

theorem LSigma_two_equiv_ISigma_two : 𝗟𝚺 2 ≊ 𝗜𝚺 2 := LSigma_equiv_ISigma 2

theorem ISigma_zero_weakerThan_BSigma_one : 𝗜𝚺 0 ⪯ 𝗕𝚺 1 := ISigma_weakerThan_BSigma_succ 0

theorem ISigma_one_weakerThan_BSigma_two : 𝗜𝚺 1 ⪯ 𝗕𝚺 2 := ISigma_weakerThan_BSigma_succ 1

theorem ISigma_two_weakerThan_PA : 𝗜𝚺 2 ⪯ 𝗣𝗔 := inferInstance

end FFL.FirstOrder.Arithmetic
