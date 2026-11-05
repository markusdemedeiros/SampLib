import Samplers.Uniform

/-! Object-language lists: nil = inl(unit), cons(x,xs) = inr((x,xs)).
These are support routines, not host-language sampler implementations. -/
namespace Occil
open ProbLang
variable {rT : Type _}

@[pl_fold] def length : Exp rT := pl%
  rec len xs := case! xs | inl(u) => #0 | inr(p) => #1 + len (snd(p))

@[pl_fold] def sumInts : Exp rT := pl%
  rec sum xs := case! xs | inl(u) => #0 | inr(p) => (fst(p)) + sum (snd(p))

@[pl_fold] def getAt : Exp rT := pl%
  rec get xs i := case! xs | inl(u) => fail | inr(p) =>
    if i = #0 then (fst(p)) else get (snd(p)) (i - #1)

/-- Returns (selected item, remaining list). -/
@[pl_fold] def removeAt : Exp rT := pl%
  rec remove xs i := case! xs | inl(u) => fail | inr(p) =>
    if i = #0 then ((fst(p)), (snd(p))) else
      let q := remove (snd(p)) (i - #1);
      ((fst(q)), inr(((fst(p)), (snd(q)))))

@[pl_fold] def insertReal : Exp rT := pl%
  rec insert x xs := case! xs
    | inl(u) => inr((x, inl(#())))
    | inr(p) => if x <= (fst(p)) then inr((x, xs)) else
        inr(((fst(p)), insert x (snd(p))))

/-- Build a list of n independent calls to a unit-taking sampler. -/
@[pl_fold] def repeatSample : Exp rT := pl%
  rec draw sampler n := if n <= #0 then inl(#()) else
    let x := sampler #();
    inr((x, draw sampler (n - #1)))

end Occil
