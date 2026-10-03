# Figure 18: Fiat-Shamir transform

Paper parameters: seed 42, 200 benchmark rounds, and attribute counts
`n = 4, 8, 32, 64`.

| n | Obt1 [ms] | Iss [ms] | Obt2 [ms] | creq [KiB] | bcred [KiB] | cred [KiB] | Present [ms] | VfPres [ms] | pres [KiB] |
|---:|----------:|---------:|----------:|-----------:|------------:|-----------:|-------------:|-------------:|-----------:|
| 4  | 3.41 | 2.53 | 0.69 | 1.1 | 0.2 | 0.1 | 1.09 | 0.80 | 0.6 |
| 8  | 4.11 | 3.27 | 0.68 | 1.6 | 0.2 | 0.1 | 1.21 | 0.85 | 1.0 |
| 32 | 9.21 | 8.19 | 0.69 | 4.6 | 0.2 | 0.1 | 2.59 | 1.96 | 3.2 |
| 64 | 15.27 | 14.64 | 0.70 | 8.6 | 0.2 | 0.1 | 3.70 | 2.97 | 6.2 |

Timings vary by hardware. The tested dimensions and serialized payload sizes
are the principal stable comparison points.
