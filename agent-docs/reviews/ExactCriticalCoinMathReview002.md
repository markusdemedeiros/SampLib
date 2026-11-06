# Critical coin mathematics: polish follow-up

Reviewer: `/root`. Supporting design review, supplementing review001; the sampler
acceptance remains the independently reviewed receipt015.

The requested explicit recurrence is now `deficit_succ`. The proof of
`missing_le` uses it directly: unresolved tail mass plus false-tail mass times
retry deficit, divided by two. The bound first replaces retry deficit by the
common survival bound, then uses false-tail mass at most one minus tail deficit.
Monotonicity in the remaining tail deficit yields `s-s^2/2`. This resolves the
presentation request without changing the domain or invoking a finite mean
runtime. No further mathematical polish requested.

Inspected source: `SampLib/Distributions/CriticalCoin.lean`: `343f481d9f80ff41493cba9a3a818ac03e81579072d516da5b2ed0d018d7e150`.
