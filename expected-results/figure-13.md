# Figure 13: Fischlin transform

Paper parameters: seed 42, 200 benchmark rounds, Fischlin work factor
`W_work = 32`, and attribute counts `n = 4, 8, 32, 64`.

| n | Obt1 [ms] | Iss [ms] | Obt2 [ms] | creq [KiB] | bcred [KiB] | cred [KiB] | Present [ms] | VfPres [ms] | pres [KiB] |
|---:|----------:|---------:|----------:|-----------:|------------:|-----------:|-------------:|-------------:|-----------:|
| 4  | 9.35 | 8.57 | 0.69 | 19.9 | 0.2 | 0.1 | 1.09 | 0.80 | 0.6 |
| 8  | 12.12 | 10.92 | 0.68 | 29.8 | 0.2 | 0.1 | 1.21 | 0.85 | 1.0 |
| 32 | 33.02 | 26.93 | 0.69 | 89.0 | 0.2 | 0.1 | 2.59 | 1.96 | 3.2 |
| 64 | 62.07 | 47.41 | 0.70 | 168 | 0.2 | 0.1 | 3.70 | 2.97 | 6.2 |

Timings vary by hardware. The tested dimensions and serialized payload sizes
are the principal stable comparison points.
