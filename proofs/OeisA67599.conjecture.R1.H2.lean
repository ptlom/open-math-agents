import OMAReductions.R_OeisA67599_conjecture_R1

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hprime
  have hne : q ≠ 7 := by omega
  have hne' : 7 ≠ q := Ne.symm hne
  have hprod : ([7, 7, 7, 7, q] : List ℕ).prod = 2401 * q := by
    simp [List.prod_cons, ← Nat.mul_assoc]
  have hfac : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
    symm
    refine List.Perm.eq_of_pairwise' ?_ (Nat.primeFactorsList_sorted _).pairwise ?_
    · simp [List.pairwise_cons, Nat.le_of_lt hq]
    · apply Nat.primeFactorsList_unique hprod
      intro p hp
      simp at hp
      rcases hp with rfl | rfl
      · decide
      · exact hprime
  have hbig : ¬ 2401 * q < 2 := by omega
  simp [OeisA67599.a, hbig, hfac, List.dedup_cons_of_mem, List.dedup_cons_of_notMem,
    List.count_cons, hne, hne', OeisA67599.concatenateNats]
  omega
