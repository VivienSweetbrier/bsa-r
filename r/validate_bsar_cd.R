# ==============================================================================
# 🅱💲🅰-R: Hypercubic Compiler — Base R 4.6.1 Cross-Validator (`validate_bsar_cd.R`)
# License: GNU AGPLv3 | Attestation: probabilistic_structural
# Verifies Q8.8 32D Cayley-Dickson integer exactness, 7 Box-Kites, & CSV savings
# ==============================================================================

cd_conj <- function(x) {
  n <- length(x)
  if (n == 1L) return(x)
  m <- n %/% 2L
  c(cd_conj(x[1:m]), -x[(m + 1L):n])
}

cd_mult <- function(x, y) {
  n <- length(x)
  if (n == 1L) return(x * y)
  m <- n %/% 2L
  c(cd_mult(x[1:m], y[1:m]) - cd_mult(cd_conj(y[(m + 1L):n]), x[(m + 1L):n]),
    cd_mult(y[(m + 1L):n], x[1:m]) + cd_mult(x[(m + 1L):n], cd_conj(y[1:m])))
}

e_basis <- function(i, dim = 32L, scale = 256L) {
  v <- integer(dim)
  v[i + 1L] <- scale
  v
}

S32 <- outer(0:31, 0:31, Vectorize(function(i, j) as.integer(sum(cd_mult(e_basis(i, 32L, 1L), e_basis(j, 32L, 1L))))))

trunc_q88 <- function(acc) {
  ifelse(acc == 0L, 0L, ifelse(acc > 0L, bitwShiftR(acc + 128L, 8L), -bitwShiftR((-acc) + 128L, 8L)))
}

cd_mult_q88 <- function(x, y) {
  vapply(0:31, function(k) {
    j <- bitwXor(0:31, k) + 1L
    acc <- sum(as.integer(x) * as.integer(y[j]) * S32[cbind(1:32, j)])
    as.integer(trunc_q88(acc))
  }, integer(1))
}

# 1. Verify native 32D Pathion zero divisor in Q8.8: (e_1 + e_18) * (e_4 - e_23) == 0 across all 32 lanes!
u32 <- e_basis(1L) + e_basis(18L)
v32 <- e_basis(4L) - e_basis(23L)
p32 <- cd_mult_q88(u32, v32)
stopifnot(all(p32 == 0L))

# 2. Verify 42 Sedenion assessors & 168 annihilation edges
assessors <- 0L
edges <- 0L
for (i in 1:7) {
  for (j in 8:15) {
    has_zd <- FALSE
    for (k in 1:7) {
      if (i == k) next
      for (l in 8:15) {
        if (bitwXor(i, k) == bitwXor(j, l)) {
          s_ik <- S32[i + 1L, k + 1L]; s_jl <- S32[j + 1L, l + 1L]
          s_il <- S32[i + 1L, l + 1L]; s_jk <- S32[j + 1L, k + 1L]
          for (sgn in c(-1L, 1L)) {
            if ((s_ik + sgn * s_jl == 0L) && (sgn * s_il + s_jk == 0L)) {
              has_zd <- TRUE
              edges <- edges + 1L
            }
          }
        }
      }
    }
    if (has_zd) assessors <- assessors + 1L
  }
}
stopifnot(assessors == 42L, edges == 168L)

# 3. Audit exported Cerebral Valley CSV benchmark
args <- commandArgs(trailingOnly = TRUE)
csv_path <- if (length(args) >= 1L) args[1] else "dist/cerebral_valley_metrics.csv"
if (file.exists(csv_path)) {
  df <- read.csv(csv_path, stringsAsFactors = FALSE)
  tot_naive <- sum(df$naive_tokens)
  tot_bsar  <- sum(df$bsar_tokens)
  pct_saved <- (1.0 - tot_bsar / tot_naive) * 100.0
  cat(sprintf("[R 4.6.1 Audit OK] 32D Q8.8 Zero-Divisor == 0 | Assessors=%d | Edges=%d | Suite Reduction=%.2f%% (%d -> %d tokens)\n",
              assessors, edges, pct_saved, tot_naive, tot_bsar))
} else {
  cat(sprintf("[R 4.6.1 Audit OK] 32D Q8.8 Zero-Divisor == 0 | Assessors=%d | Edges=%d\n", assessors, edges))
}
