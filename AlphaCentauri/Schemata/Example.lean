module

public import AlphaCentauri.Schemata.Collection.Equivalence
public import AlphaCentauri.Schemata.Collection.Induction
public import AlphaCentauri.Schemata.LeastNumber.Basic

/-!
# Instances of the fragment hierarchy

The relations between the fragments are stated for every index, which leaves the theory zoo — whose
vertices are closed theories — with nothing to draw. These are their instances at the first few
indices.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

theorem BSigma1_weakerThan_ISigma1 : 𝗕𝚺 1 ⪯ 𝗜𝚺 1 := BSigma_weakerThan_ISigma 0

theorem BSigma2_weakerThan_ISigma2 : 𝗕𝚺 2 ⪯ 𝗜𝚺 2 := BSigma_weakerThan_ISigma 1

theorem BSigma1_equiv_BPi0 : 𝗕𝚺 1 ≊ 𝗕𝚷 0 := BSigma_succ_equiv_BPi 0

theorem BSigma2_equiv_BPi1 : 𝗕𝚺 2 ≊ 𝗕𝚷 1 := BSigma_succ_equiv_BPi 1

theorem ISigma1_equiv_IPi1 : 𝗜𝚺 1 ≊ 𝗜𝚷 1 := ISigma_equiv_IPi 1

theorem ISigma2_equiv_IPi2 : 𝗜𝚺 2 ≊ 𝗜𝚷 2 := ISigma_equiv_IPi 2

theorem LSigma1_equiv_ISigma1 : 𝗟𝚺 1 ≊ 𝗜𝚺 1 := LSigma_equiv_ISigma 1

theorem LPi1_equiv_ISigma1 : 𝗟𝚷 1 ≊ 𝗜𝚺 1 := LPi_equiv_ISigma 1

theorem LSigma2_equiv_ISigma2 : 𝗟𝚺 2 ≊ 𝗜𝚺 2 := LSigma_equiv_ISigma 2

theorem ISigma0_weakerThan_BSigma1 : 𝗜𝚺 0 ⪯ 𝗕𝚺 1 := ISigma_weakerThan_BSigma_succ 0

theorem ISigma1_weakerThan_BSigma2 : 𝗜𝚺 1 ⪯ 𝗕𝚺 2 := ISigma_weakerThan_BSigma_succ 1

theorem ISigma2_weakerThan_PA : 𝗜𝚺 2 ⪯ 𝗣𝗔 := inferInstance

end FFL.FirstOrder.Arithmetic
