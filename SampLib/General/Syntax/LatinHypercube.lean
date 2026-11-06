import SampLib.General.LatinHypercube1D

/-! # Closedness of shuffled stratification under repetition -/

open ProbLang

namespace SampLib.LatinHypercube1D

theorem latinHypercube1D_lc {rT : Type _} :
    (Occil.General.latinHypercube1D : Exp rT).IsLocallyClosed := by is_lc

theorem latinHypercube1D_fv {rT : Type _} :
    (Occil.General.latinHypercube1D : Exp rT).fv = ∅ := by
  simp [Occil.General.latinHypercube1D, Exp.fv, Shuffle.shuffle_fv,
    Stratified1D.stratified1D_fv]

@[simp] theorem latinHypercube1D_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.latinHypercube1D = Occil.General.latinHypercube1D :=
  (Exp.open_lc k e _ latinHypercube1D_lc).symm

@[simp] theorem latinHypercube1D_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.latinHypercube1D : Exp rT) =
      Occil.General.latinHypercube1D :=
  Exp.closeRec_fresh x _ k (by simp [latinHypercube1D_fv])

end SampLib.LatinHypercube1D

/- Curried value witnesses keep the symbolic execution of large closures folded. -/
namespace SampLib.LatinHypercube.Source

def sourceValue {rT : Type _} : Val rT :=
  ⟨Occil.General.latinHypercube, .lam (by is_lc), by is_lc⟩

theorem sourceValue_fst {rT : Type _} :
    (sourceValue (rT := rT)).fst = Occil.General.latinHypercube := rfl

def countStage {rT : Type _} (scale : ℕ) : Val rT :=
  ⟨pl(fun count dimension u,
    if dimension <= #0 then fail else
      let columns := &Occil.repeatSample
        (fun u, &Occil.General.latinHypercube1D #int (scale : ℤ) count #()) dimension;
      let rows := (rec build index := if index = count then inl(#()) else
        inr((&Occil.General.map (fun column, &Occil.getAt column index) columns,
          build (index + #1))));
      rows #0), .lam (by is_lc), by is_lc⟩

theorem countStage_fst {rT : Type _} (scale : ℕ) :
    (countStage (rT := rT) scale).fst = pl(fun count dimension u,
    if dimension <= #0 then fail else
      let columns := &Occil.repeatSample
        (fun u, &Occil.General.latinHypercube1D #int (scale : ℤ) count #()) dimension;
      let rows := (rec build index := if index = count then inl(#()) else
        inr((&Occil.General.map (fun column, &Occil.getAt column index) columns,
          build (index + #1))));
      rows #0) := rfl

def dimensionStage {rT : Type _} (scale count : ℕ) : Val rT :=
  ⟨pl(fun dimension u,
    if dimension <= #0 then fail else
      let columns := &Occil.repeatSample
        (fun u, &Occil.General.latinHypercube1D #int (scale : ℤ) #int (count : ℤ) #()) dimension;
      let rows := (rec build index := if index = #int (count : ℤ) then inl(#()) else
        inr((&Occil.General.map (fun column, &Occil.getAt column index) columns,
          build (index + #1))));
      rows #0), .lam (by is_lc), by is_lc⟩

theorem dimensionStage_fst {rT : Type _} (scale count : ℕ) :
    (dimensionStage (rT := rT) scale count).fst = pl(fun dimension u,
    if dimension <= #0 then fail else
      let columns := &Occil.repeatSample
        (fun u, &Occil.General.latinHypercube1D #int (scale : ℤ) #int (count : ℤ) #()) dimension;
      let rows := (rec build index := if index = #int (count : ℤ) then inl(#()) else
        inr((&Occil.General.map (fun column, &Occil.getAt column index) columns,
          build (index + #1))));
      rows #0) := rfl

def unitStage {rT : Type _} (scale count dimension : ℕ) : Val rT :=
  ⟨pl(fun u,
    if #int (dimension : ℤ) <= #0 then fail else
      let columns := &Occil.repeatSample
        (fun u, &Occil.General.latinHypercube1D #int (scale : ℤ) #int (count : ℤ) #())
        #int (dimension : ℤ);
      let rows := (rec build index := if index = #int (count : ℤ) then inl(#()) else
        inr((&Occil.General.map (fun column, &Occil.getAt column index) columns,
          build (index + #1))));
      rows #0), .lam (by is_lc), by is_lc⟩

theorem unitStage_fst {rT : Type _} (scale count dimension : ℕ) :
    (unitStage (rT := rT) scale count dimension).fst = pl(fun u,
    if #int (dimension : ℤ) <= #0 then fail else
      let columns := &Occil.repeatSample
        (fun u, &Occil.General.latinHypercube1D #int (scale : ℤ) #int (count : ℤ) #())
        #int (dimension : ℤ);
      let rows := (rec build index := if index = #int (count : ℤ) then inl(#()) else
        inr((&Occil.General.map (fun column, &Occil.getAt column index) columns,
          build (index + #1))));
      rows #0) := rfl

end SampLib.LatinHypercube.Source
