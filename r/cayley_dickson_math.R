# ==============================================================================
# 🅱💲🅰-R Mathematical Research Companion for Base R (`r/cayley_dickson_math.R`)
# License: GNU AGPLv3 | Attestation: probabilistic_structural
# Zero External R Dependencies (Base R >= 4.1.0, verified on R 4.6.1)
#
# Provides pure-R computational probes for:
#   1. Arbitrary 2^n-ions & split signatures gamma in {-1, +1}^n (G. P. Wilmot)
#   2. Left/Right multiplication operators L_x, R_x, Koebisu's sedenion quartic
#      det(L_x) = ||x||^8 * Q(x)^2 factorization, & Moreno's dim ker(L_x) = 4k
#      annihilator spectrum (Moreno, Reggiani, Koebisu)
#   3. Relation graph data.frames (`zero_divisor`, `commutativity`,
#      `mutual_alternativity`) ready for native `|>` pipes (Guterman & Zhilina)
# ==============================================================================

#' @title Compile Arbitrary-Signature Cayley-Dickson XOR Sign Matrix
#' @description Compiles the exact `2^n x 2^n` basis sign matrix `S` satisfying
#' `e_i * e_j = S[i+1, j+1] * e_{i XOR j}` for any doubling signature vector
#' `gamma` in `c(-1L, 1L)^n` (`gamma = rep(-1L, n)` gives standard real CD).
#' @param level Non-negative integer `n` (`dim = 2^n`; `4L` = 16D, `5L` = 32D).
#' @param gamma Integer vector of length `level` with entries in `c(-1L, 1L)`.
#' @return Integer matrix of dimension `2^level x 2^level`.
#' @export
cd_sign_matrix_gamma <- function(level = 4L, gamma = rep(-1L, level)) {
  level <- as.integer(level)
  if (is.na(level) || level < 0L || level > 8L) {
    stop("`level` must be an integer in 0..8.")
  }
  if (level == 0L) {
    return(matrix(1L, nrow = 1L, ncol = 1L))
  }
  gamma <- as.integer(gamma)
  if (length(gamma) != level || any(!(gamma %in% c(-1L, 1L)))) {
    stop("`gamma` must have length `level` with entries in c(-1L, 1L).")
  }
  s_half <- cd_sign_matrix_gamma(level - 1L, gamma[seq_len(level - 1L)])
  half <- bitwShiftL(1L, level - 1L)
  dim_n <- bitwShiftL(1L, level)
  g_cur <- gamma[level]
  conj_s <- c(1L, rep(-1L, half - 1L))
  out <- matrix(0L, nrow = dim_n, ncol = dim_n)

  for (i in 0:(dim_n - 1L)) {
    for (j in 0:(dim_n - 1L)) {
      if (i < half && j < half) {
        sgn <- s_half[i + 1L, j + 1L]
      } else if (i < half && j >= half) {
        sgn <- s_half[(j - half) + 1L, i + 1L]
      } else if (i >= half && j < half) {
        sgn <- conj_s[j + 1L] * s_half[(i - half) + 1L, j + 1L]
      } else {
        d_idx <- j - half
        b_idx <- i - half
        sgn <- g_cur * conj_s[d_idx + 1L] * s_half[d_idx + 1L, b_idx + 1L]
      }
      out[i + 1L, j + 1L] <- as.integer(sgn)
    }
  }
  out
}

#' @title Left Multiplication Operator Matrix L_x
#' @description Constructs the exact `dim x dim` left-multiplication matrix `L_x`
#' (`y |-> x * y`) from a precomputed Cayley-Dickson sign matrix `S`.
#' @export
cd_left_mult_matrix <- function(x, S = cd_sign_matrix_gamma(as.integer(round(log2(length(x)))))) {
  n <- length(x)
  L <- matrix(0, nrow = n, ncol = n)
  nz <- which(x != 0)
  for (idx_i in nz) {
    i0 <- idx_i - 1L
    xi <- x[idx_i]
    for (j0 in 0:(n - 1L)) {
      k0 <- bitwXor(i0, j0)
      L[k0 + 1L, j0 + 1L] <- L[k0 + 1L, j0 + 1L] + xi * S[idx_i, j0 + 1L]
    }
  }
  L
}

#' @title Right-Annihilator Dimension (`dim ker(L_x)`) & Basis via QR/SVD
#' @description Computes `dim ker(L_x)` (verifying Moreno's `4k` law) and returns
#' an orthonormal basis for the right annihilator `{y : x * y = 0}`.
#' @export
cd_annihilator_profile <- function(x, S = NULL, tol = 1e-10) {
  if (is.null(S)) {
    lvl <- as.integer(round(log2(length(x))))
    S <- cd_sign_matrix_gamma(lvl)
  }
  L <- cd_left_mult_matrix(x, S)
  sv <- svd(L)
  null_mask <- sv$d <= (tol * max(1, max(sv$d)))
  nullity <- sum(null_mask)
  basis <- if (nullity > 0L) sv$v[, null_mask, drop = FALSE] else matrix(0, nrow = length(x), ncol = 0L)
  list(
    dim = length(x),
    nullity = as.integer(nullity),
    moreno_mod4_ok = (nullity %% 4L == 0L),
    singular_values = sv$d,
    basis = basis
  )
}

#' @title Audit Koebisu Sedenion Determinant Factorization (`arXiv:2512.13002`)
#' @description Compares `det(L_x)` against `||x||^8 * Q(x)^2` and returns the
#' four non-negative Stiefel `V_2(R^7)` sum-of-squares zero-divisor obstructions.
#' @export
cd_koebisu_sedenion_audit <- function(x) {
  if (length(x) != 16L) {
    stop("Koebisu's sedenion determinant factorization requires a 16-vector `x`.")
  }
  S16 <- cd_sign_matrix_gamma(4L, rep(-1L, 4L))
  L <- cd_left_mult_matrix(x, S16)
  det_num <- det(L)

  a0 <- x[1L]; va <- x[2:8]
  b0 <- x[9L]; vb <- x[10:16]
  nx2 <- sum(x * x)
  nva2 <- sum(va * va)
  nvb2 <- sum(vb * vb)
  dot_ab <- sum(va * vb)

  s0 <- a0 * a0 + b0 * b0
  quartic_q <- s0 * s0 + 2 * s0 * (nva2 + nvb2) + (nva2 - nvb2)^2 + 4 * dot_ab^2
  det_koebisu <- (nx2^4) * (quartic_q^2)

  list(
    det_matrix = det_num,
    det_koebisu = det_koebisu,
    rel_error = if (det_koebisu == 0) abs(det_num) else abs(det_num - det_koebisu) / det_koebisu,
    norm_x_sq = nx2,
    quartic_Q = quartic_q,
    is_stiefel_zero_divisor = (nx2 > 0 && quartic_q == 0)
  )
}

#' @title Build Guterman-Zhilina Relation Graph `data.frame`
#' @description Enumerates `zero_divisor` and `commutativity` edges across primitive
#' cross-half assessors for standard or split Cayley-Dickson algebras, ready for `|>`.
#' @export
cd_relation_edges_df <- function(level = 4L, gamma = rep(-1L, level)) {
  S <- cd_sign_matrix_gamma(level, gamma)
  dim_n <- bitwShiftL(1L, level)
  half <- dim_n %/% 2L

  mult_sparse <- function(i, si, j, sj, k, sk, l, sl) {
    acc <- numeric(dim_n)
    pairs_u <- list(c(i, si), c(j, sj))
    pairs_v <- list(c(k, sk), c(l, sl))
    for (pu in pairs_u) {
      for (pv in pairs_v) {
        u_idx <- pu[1L]; u_s <- pu[2L]
        v_idx <- pv[1L]; v_s <- pv[2L]
        t_idx <- bitwXor(u_idx, v_idx) + 1L
        acc[t_idx] <- acc[t_idx] + u_s * v_s * S[u_idx + 1L, v_idx + 1L]
      }
    }
    acc
  }

  verts <- list()
  ptr_v <- 0L
  for (i in 1:(half - 1L)) {
    for (j in half:(dim_n - 1L)) {
      if (j == bitwXor(i, half)) next
      for (sgn in c(1L, -1L)) {
        ptr_v <- ptr_v + 1L
        verts[[ptr_v]] <- list(
          label = sprintf("e%d%se%d", i, if (sgn > 0L) "+" else "-", j),
          i = i, j = j, sgn = sgn
        )
      }
    }
  }

  edges <- list()
  ptr_e <- 0L
  nv <- length(verts)
  for (a in seq_len(nv - 1L)) {
    va <- verts[[a]]
    for (b in (a + 1L):nv) {
      vb <- verts[[b]]
      if (va$i == vb$i && va$j == vb$j) next
      uv <- mult_sparse(va$i, 1L, va$j, va$sgn, vb$i, 1L, vb$j, vb$sgn)
      vu <- mult_sparse(vb$i, 1L, vb$j, vb$sgn, va$i, 1L, va$j, va$sgn)
      if (all(uv == 0) && all(vu == 0)) {
        ptr_e <- ptr_e + 1L
        edges[[ptr_e]] <- data.frame(
          relation = "zero_divisor", u = va$label, v = vb$label, stringsAsFactors = FALSE
        )
      }
      if (all(uv == vu)) {
        ptr_e <- ptr_e + 1L
        edges[[ptr_e]] <- data.frame(
          relation = "commutativity", u = va$label, v = vb$label, stringsAsFactors = FALSE
        )
      }
    }
  }
  if (ptr_e == 0L) {
    return(data.frame(relation = character(0), u = character(0), v = character(0)))
  }
  do.call(rbind, edges[seq_len(ptr_e)])
}

#' @title Single-Pass Functional Round-4 Shell Dispersion `Theta` (`Reduce` Moore Fold)
#' @description Computes Round 4's spectral moments `(M0, D, P)`, variance numerator
#' `M0 * P - D^2`, and normalized dispersion `Theta` in one functional `Reduce` pass
#' across both the `Z_2` doubling shells `(-1, +1)` and the dyadic bit-length filtration.
#' @export
cd_shell_dispersion <- function(x) {
  n <- length(x)
  if (n < 4L || bitwAnd(n, n - 1L) != 0L) {
    stop("`x` must have power-of-two length >= 4.")
  }
  half <- n %/% 2L

  run_moore_fold <- function(pairs_list) {
    step_fn <- function(st, pair) {
      m_val <- pair[1L]
      e_val <- pair[2L]
      c(st[1L] + e_val, st[2L] + m_val * e_val, st[3L] + (m_val * m_val) * e_val)
    }
    acc <- Reduce(step_fn, pairs_list, init = c(0, 0, 0))
    m0 <- acc[1L]; d_val <- acc[2L]; p_val <- acc[3L]
    var_num <- m0 * p_val - d_val * d_val
    denom <- m0 * p_val
    list(
      M0 = m0,
      D = d_val,
      P = p_val,
      variance_M0P_minus_D2 = var_num,
      is_monochromatic_zero_variance = (abs(var_num) <= 1e-12),
      theta_dispersion = if (denom > 0) var_num / denom else 0
    )
  }

  s0_sq <- x[1L]^2 + x[half + 1L]^2
  e_low <- sum(x[2:half]^2)
  e_high <- sum(x[(half + 2L):n]^2)
  z2_res <- run_moore_fold(list(c(-1, e_low), c(1, e_high)))

  bit_len <- function(k0) {
    if (k0 <= 0L) return(0L)
    as.integer(floor(log2(k0)) + 1L)
  }
  nz <- which(x != 0)
  dyadic_pairs <- lapply(nz, function(idx1) c(bit_len(idx1 - 1L), x[idx1]^2))
  dyadic_res <- run_moore_fold(dyadic_pairs)

  list(
    dim = n,
    s0_heads_sq = s0_sq,
    e_low_im = e_low,
    e_high_im = e_high,
    z2_bimodal = z2_res,
    dyadic_filtration = dyadic_res
  )
}

#' @title Pure Functional Coalgebraic Minimal FSM Extractor (`S / ~`) in Base R
#' @description Runs Moore/Hopcroft coalgebraic bisimulation partition refinement
#' until fixed-point convergence on a finite state vector `states`, returning tidy
#' `transitions_df` and `classes_df` ready for Base R `|>` pipelines.
#' @export
discover_minimal_fsm_r <- function(states, alphabet, step_fn, obs_fn) {
  states <- as.character(states)
  alphabet <- as.character(alphabet)
  n_s <- length(states)
  idx_map <- setNames(seq_len(n_s), states)

  raw_obs <- vapply(states, function(s) as.character(obs_fn(s)), character(1L))
  trans_idx <- lapply(states, function(s) {
    vapply(alphabet, function(a) idx_map[[as.character(step_fn(s, a))]], integer(1L))
  })

  encode_blocks <- function(keys) {
    uniq <- unique(keys)
    match(keys, uniq) - 1L
  }

  block_of <- encode_blocks(raw_obs)
  rounds <- 0L
  repeat {
    rounds <- rounds + 1L
    sigs <- vapply(seq_len(n_s), function(i) {
      dst_b <- block_of[trans_idx[[i]]]
      paste(c(block_of[i], dst_b), collapse = ":")
    }, character(1L))
    next_block <- encode_blocks(sigs)
    if (length(unique(next_block)) == length(unique(block_of))) {
      block_of <- next_block
      break
    }
    block_of <- next_block
  }

  num_q <- length(unique(block_of))
  q_labels <- sprintf("Q%02d", 0:(num_q - 1L))
  first_idx <- match(0:(num_q - 1L), block_of)

  classes_df <- data.frame(
    quotient_state = q_labels,
    observation = raw_obs[first_idx],
    class_size = as.integer(tabulate(block_of + 1L, nbins = num_q)),
    representative = states[first_idx],
    stringsAsFactors = FALSE
  )

  t_rows <- list()
  ptr <- 0L
  for (b0 in 0:(num_q - 1L)) {
    rep_i <- first_idx[b0 + 1L]
    for (ai in seq_along(alphabet)) {
      ptr <- ptr + 1L
      dst_i <- trans_idx[[rep_i]][ai]
      t_rows[[ptr]] <- data.frame(
        src = q_labels[b0 + 1L],
        symbol = alphabet[ai],
        dst = q_labels[block_of[dst_i] + 1L],
        stringsAsFactors = FALSE
      )
    }
  }

  list(
    raw_state_count = n_s,
    minimal_state_count = num_q,
    refinement_rounds = rounds,
    classes_df = classes_df,
    transitions_df = do.call(rbind, t_rows)
  )
}
