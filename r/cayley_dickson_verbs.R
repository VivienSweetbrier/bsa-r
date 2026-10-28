#' @title Compile Cayley-Dickson XOR Sign Matrix
#' @description Compiles the exact `dim x dim` Cayley-Dickson sign matrix `S`
#' (`S[i+1, j+1] %in% c(-1L, 1L)`) satisfying `e_i * e_j = S[i+1, j+1] * e_{i XOR j}`
#' for any power-of-two dimension (`1L, 2L, 4L, 8L, 16L, 32L, 64L`).
#' @param dim Integer power of 2 (`16L` = Sedenions, `32L` = Pathions).
#' @return Integer matrix of dimension `dim x dim` with entries in `c(-1L, 1L)`.
#' @export
cd_sign_matrix <- function(dim = 32L) {
  dim <- as.integer(dim)
  if (is.na(dim) || dim < 1L || bitwAnd(dim, dim - 1L) != 0L) {
    stop("`dim` must be a positive power of 2 (e.g., 16L for Sedenions, 32L for Pathions).")
  }
  if (dim == 1L) {
    return(matrix(1L, nrow = 1L, ncol = 1L))
  }
  half <- dim %/% 2L
  s_half <- cd_sign_matrix(half)
  conj_s <- c(1L, rep(-1L, half - 1L))
  out <- matrix(0L, nrow = dim, ncol = dim)

  for (i in 0:(dim - 1L)) {
    for (j in 0:(dim - 1L)) {
      if (i < half && j < half) {
        sgn <- s_half[i + 1L, j + 1L]
      } else if (i < half && j >= half) {
        sgn <- s_half[(j - half) + 1L, i + 1L]
      } else if (i >= half && j < half) {
        sgn <- conj_s[j + 1L] * s_half[(i - half) + 1L, j + 1L]
      } else {
        d_idx <- j - half
        b_idx <- i - half
        sgn <- -conj_s[d_idx + 1L] * s_half[d_idx + 1L, b_idx + 1L]
      }
      out[i + 1L, j + 1L] <- as.integer(sgn)
    }
  }
  out
}

#' @title Fast Vectorized Cayley-Dickson Product
#' @description Multiplies two `2^k`-dimensional hypercomplex vectors (`16D` Sedenions
#' or `32D` Pathions) using `bitwXor` index routing and precomputed sign matrix `S`.
#' @param x Numeric vector of length `2^k` (no `NaN`/`Inf`).
#' @param y Numeric vector of length `2^k` matching `length(x)`.
#' @param S Optional precomputed sign matrix from `cd_sign_matrix(length(x))`.
#' @return Numeric vector of length `length(x)`.
#' @export
cd_mult_vec <- function(x, y, S = NULL) {
  n <- length(x)
  if (length(y) != n || any(!is.finite(x)) || any(!is.finite(y))) {
    stop("`x` and `y` must be finite numeric vectors of identical power-of-two length.")
  }
  if (is.null(S)) {
    S <- cd_sign_matrix(n)
  }
  idx_0 <- 0:(n - 1L)
  vapply(idx_0, function(k) {
    j <- bitwXor(idx_0, k) + 1L
    sum(x * y[j] * S[cbind(seq_len(n), j)])
  }, numeric(1L))
}

#' @title BSA-R Single-Cache-Line Q8.8 Fixed-Point 32D Pathion Product
#' @description Multiplies two 32-lane `Q8.8` fixed-point integer vectors (`64 bytes` =
#' 1 CPU L1 cache line) with sign-symmetric shift-by-8 (`Q16.16 -> Q8.8`) and zero
#' floating-point drift.
#' @param x_q88 Integer vector of length 32 (`[-32768, 32767]`).
#' @param y_q88 Integer vector of length 32 (`[-32768, 32767]`).
#' @param S32 Optional `32x32` sign matrix from `cd_sign_matrix(32L)`.
#' @return Integer vector of length 32 in `Q8.8` format.
#' @export
cd_q88_mult <- function(x_q88, y_q88, S32 = NULL) {
  if (length(x_q88) != 32L || length(y_q88) != 32L) {
    stop("`x_q88` and `y_q88` must be 32-lane Q8.8 integer vectors (64 bytes).")
  }
  if (is.null(S32)) {
    S32 <- cd_sign_matrix(32L)
  }
  x_int <- as.integer(x_q88)
  y_int <- as.integer(y_q88)
  idx_0 <- 0:31
  vapply(idx_0, function(k) {
    j <- bitwXor(idx_0, k) + 1L
    acc <- sum(as.numeric(x_int) * as.numeric(y_int[j]) * as.numeric(S32[cbind(1:32, j)]))
    if (acc == 0) return(0L)
    sgn <- if (acc < 0) -1L else 1L
    mag <- as.integer((abs(acc) + 128) %/% 256)
    val <- sgn * mag
    max(-32768L, min(32767L, as.integer(val)))
  }, integer(1L))
}

#' @title Construct 16D Sedenion 7-Box-Kite Zero-Divisor Catalog
#' @description Enumerates all `168` directed zero-divisor annihilation edges across
#' the `42` primitive Sedenion assessors (`7` octahedral Box-Kites).
#' @return A data.frame of directed annihilation pairs `(i, j, k, l, partner_sign)`
#' satisfying `(e_i + e_j) * (e_k + partner_sign * e_l) == 0`.
#' @export
cd_boxkite_table <- function() {
  S16 <- cd_sign_matrix(16L)
  rows <- vector("list", 168L)
  ptr <- 0L
  for (i in 1:7) {
    for (j in 9:15) {
      if (j == bitwXor(i, 8L)) next
      for (k in 1:7) {
        if (i == k) next
        for (l in 9:15) {
          if (l == bitwXor(k, 8L)) next
          if (bitwXor(i, k) != bitwXor(j, l)) next
          s_ik <- S16[i + 1L, k + 1L]
          s_jl <- S16[j + 1L, l + 1L]
          s_il <- S16[i + 1L, l + 1L]
          s_jk <- S16[j + 1L, k + 1L]
          for (sgn in c(-1L, 1L)) {
            if ((s_ik + sgn * s_jl == 0L) && (sgn * s_il + s_jk == 0L)) {
              ptr <- ptr + 1L
              rows[[ptr]] <- data.frame(
                assessor_i = i,
                assessor_j = j,
                partner_k = k,
                partner_l = l,
                partner_sign = sgn,
                stringsAsFactors = FALSE
              )
            }
          }
        }
      }
    }
  }
  do.call(rbind, rows[seq_len(ptr)])
}

#' @title Audit BSA-R + 32D Pathion AI Expense Savings
#' @description Tidyverse pipe verb quantifying token and USD cost reductions from
#' `BSA-R` Hilbert CSR/CSC slicing, pre-API Porch zero-divisor bloat annihilation,
#' and `64-byte` `Q8.8` non-associative AST memoization.
#' @param .data A data.frame or tibble of agent chore runs.
#' @param raw_tokens_col Column of naive raw-context + guardrail input tokens.
#' @param bsar_tokens_col Column of `BSA-R` Hilbert-sliced input tokens.
#' @param memo_hit_col Logical column indicating a `64-byte` `Q8.8` AST cache hit.
#' @param input_usd_per_1m USD price per 1M input tokens (default `3.0`).
#' @importFrom dplyr mutate
#' @importFrom rlang `{{`
#' @export
audit_bsar_pathion_expenses <- function(
  .data,
  raw_tokens_col,
  bsar_tokens_col,
  memo_hit_col,
  input_usd_per_1m = 3.0
) {
  if (requireNamespace("dplyr", quietly = TRUE) && requireNamespace("rlang", quietly = TRUE)) {
    return(
      .data |>
        dplyr::mutate(
          effective_pathion_tokens = ifelse({{ memo_hit_col }}, 0L, {{ bsar_tokens_col }}),
          tokens_saved = {{ raw_tokens_col }} - effective_pathion_tokens,
          token_savings_pct = (tokens_saved / pmax({{ raw_tokens_col }}, 1)) * 100.0,
          usd_saved = (tokens_saved / 1e6) * input_usd_per_1m
        )
    )
  }
  # Zero-dependency Base R NSE fallback (R >= 4.1.0 native pipe `|>` compatible)
  raw_v <- eval(substitute(raw_tokens_col), .data, parent.frame())
  bsar_v <- eval(substitute(bsar_tokens_col), .data, parent.frame())
  hit_v <- as.logical(eval(substitute(memo_hit_col), .data, parent.frame()))
  out <- .data
  out[["effective_pathion_tokens"]] <- ifelse(hit_v, 0L, bsar_v)
  out[["tokens_saved"]] <- raw_v - out[["effective_pathion_tokens"]]
  out[["token_savings_pct"]] <- (out[["tokens_saved"]] / pmax(raw_v, 1)) * 100.0
  out[["usd_saved"]] <- (out[["tokens_saved"]] / 1e6) * input_usd_per_1m
  out
}
