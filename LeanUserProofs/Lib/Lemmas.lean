



namespace LeanProofs.Lib.Lemmas

abbrev Arr (t0 : Type) [Inhabited t0] : Type := Int -> t0

@[simp, grind =]
def arr_get {t0 : Type} [Inhabited t0] (arr: Arr t0) (idx: Int) : t0 :=
  arr idx

@[simp]
def arr_set {t0 : Type} [Inhabited t0] (arr: Arr t0) (idx: Int) (v: t0): Arr t0 :=
  fun i => if i = idx then v else arr i

@[grind =]
theorem set_get_neq {t0 : Type} [Inhabited t0] : ∀ (a: Arr t0) (i: Int) (v: t0) (j: Int),
   i != j -> (arr_get (arr_set a i v) j) = arr_get a j
   := by grind [arr_set]

@[grind =]
theorem set_get_eq {t0 : Type} [Inhabited t0] : ∀ (a : Arr t0) (i : Int) (v : t0),
   (arr_get (arr_set a i v) i) = v := by grind [arr_set]

@[grind =]
theorem set_get_neq' {t0 : Type} [Inhabited t0] : ∀ (a: Arr t0) (i: Int) (v: t0) (j: Int),
   i != j -> (arr_set a i v) j = a j
   := by grind [arr_set]

@[grind =]
theorem set_get_eq' {t0 : Type} [Inhabited t0] : ∀ (a : Arr t0) (i : Int) (v : t0),
   (arr_set a i v) i = v := by grind [arr_set]

end LeanProofs.Lib.Lemmas



-- def biggerList (a: List Int) (x: Int) : Prop :=
--   forall (i : Nat), i < a.length -> a[i]! <= x

-- def biggerArray (a: Array Int) (x: Int) : Prop :=
--   forall (i : Nat), i < a.size -> a[i]! <= x

-- theorem bigger_equiv: ∀ (xs: Array Int) (a: Int),
--   biggerArray xs a <-> biggerList xs.toList a := by
--   intros xs a
--   apply Iff.intro <;> simp_all [biggerArray, biggerList]

-- theorem append_get_l: ∀ (xs ys: List Int) (i: Nat),
--   (i < xs.length) -> (xs ++ ys)[i]! = xs[i]! := by
--   intros xs ys i i_lt_xs
--   induction xs generalizing i <;> grind

-- theorem append_get_r: ∀ (xs ys: List Int) (i: Nat),
--   (¬ i < xs.length) -> (xs ++ ys)[i]! = ys[i - xs.length]! := by
--   intros xs ys i i_lt_xs
--   induction xs generalizing i <;> grind

-- theorem append_get_l': ∀ (xs ys: Array Int) (i: Nat),
--   (i < xs.size) -> (xs ++ ys)[i]! = xs[i]! := by
--   intros xs ys i i_lt_xs
--   induction xs generalizing i <;> grind

-- theorem append_get_r': ∀ (xs ys: Array Int) (i: Nat),
--   (¬ i < xs.size) -> (xs ++ ys)[i]! = ys[i - xs.size]! := by
--   intros xs ys i i_lt_xs
--   induction xs generalizing i <;> grind

-- theorem append_sorted : ∀ (xs ys: Array Int),
--   sort_is_sorted xs -> sort_is_sorted ys ->
--   (∀ i j, i < xs.size -> j < ys.size -> xs[i]! <= ys[j]!) ->
--    sort_is_sorted (Array.append xs ys) := by
--    intros xs ys
--    simp [sort_is_sorted, is_sorted_between]
--    -- intros i j i_pos i_lt_j j_lt_size
--    intros xsorted ysorted cross i j i_lt_j j_lt_size
--    by_cases h : i < xs.size
--    case pos =>
--       by_cases h' : j < xs.size
--       case pos =>
--       -- i < xs.size, j < xs.size
--         grind
--       case neg =>
--       -- i < xs.size, ¬ j < xs.size
--         have lhs : (xs ++ ys)[i]! = xs[i]! := by
--           grind [append_get_l']
--         have rhs : (xs ++ ys)[j]! = ys[j - xs.size]! := by
--           grind [append_get_r']
--         grind
--    case neg =>
--       by_cases h' : j < xs.size
--       case pos =>
--      -- ¬ (i < xs.size), j < xs.size
--         grind
--       case neg =>
--      -- ¬ (i < xs.size), ¬ j < xs.size
--         have lhs : (xs ++ ys)[i]! = ys[i - xs.size]! := by
--           grind [append_get_r']
--         have rhs : (xs ++ ys)[j]! = ys[j - xs.size]! := by
--           grind [append_get_r']
--         have between : i - xs.size < j - xs.size := by
--           grind
--         simp [lhs, rhs]
--         apply ysorted <;> grind

-- theorem empty_bigger: ∀ (a: Int), biggerArray Array.empty a := by
--   simp [biggerArray]; intros; contradiction

-- theorem empty_sorted : sort_is_sorted Array.empty := by
--   intros
--   simp [sort_is_sorted, is_sorted_between]
--   intros i j i_lt_j j_lt_size
--   contradiction

-- theorem singleton_sorted : ∀ (x: Int), sort_is_sorted (Array.singleton x) := by
--   simp [sort_is_sorted, is_sorted_between]
--   grind

-- theorem array_push_empty_singleton: ∀ (x: Int), Array.push Array.empty x = Array.singleton x := by
--   intros x
--   simp [Array.push, Array.singleton]
--   rfl

-- theorem singleton_sorted' : ∀ (x: Int), sort_is_sorted (Array.push Array.empty x) := by
--   simp [array_push_empty_singleton]
--   apply singleton_sorted

-- @[simp]
-- theorem push_is_append_singleton : ∀ (xs: Array Int) (x: Int),
--   Array.push xs x = Array.append xs (Array.singleton x) := by
--   intros xs x
--   simp [Array.push, Array.append, Array.singleton]

-- theorem push_sorted : ∀ (xs: Array Int) (x: Int),
--   sort_is_sorted xs -> biggerArray xs x -> sort_is_sorted (Array.push xs x) := by
--   intros
--   rw [push_is_append_singleton]
--   apply append_sorted
--   . assumption
--   . apply singleton_sorted
--   . simp_all [biggerArray]

-- theorem append_bigger: ∀ (xs ys: List Int) (a: Int),
--   biggerList xs a -> biggerList ys a -> biggerList (xs ++ ys) a := by
--   intros xs ys a xs_bigger ys_bigger
--   simp_all [biggerList]
--   intros i i_lt_size
--   by_cases h : i < xs.length
--   case pos =>
--     have at_i : (xs ++ ys)[i]! = xs[i]! := by grind [append_get_l]
--     grind
--   case neg =>
--     have at_i : (xs ++ ys)[i]! = ys[i - xs.length]! := by grind [append_get_r]
--     grind

-- theorem append_bigger_array: ∀ (xs ys: Array Int) (a: Int),
--   biggerArray xs a -> biggerArray ys a -> biggerArray (Array.append xs ys) a
--   := by
--   intros xs ys a xs_bigger ys_bigger
--   simp_all [biggerArray]
--   intros i i_lt_size
--   by_cases h : i < xs.size
--   case pos =>
--     have at_i : (xs ++ ys)[i]! = xs[i]! := by grind [append_get_l]
--     grind
--   case neg =>
--     have at_i : (xs ++ ys)[i]! = ys[i - xs.size]! := by grind [append_get_r]
--     grind

-- theorem push_bigger: ∀ (xs: List Int) (x a: Int),
--   biggerList xs a -> x <= a -> biggerList (xs ++ [x]) a := by
--   intros xs x a xs_bigger x_le_a
--   apply append_bigger
--   . assumption
--   . simp [biggerList]; assumption

-- theorem push_bigger_array: ∀ (xs: Array Int) (x a: Int),
--   biggerArray xs a -> x <= a -> biggerArray (Array.push xs x) a := by
--   intros xs x a xs_bigger x_le_a
--   rw [push_is_append_singleton]
--   apply append_bigger_array
--   . assumption
--   . simp [biggerArray]; assumption
