use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, MultiscalarMul, VartimeMultiscalarMul};
use rayon::prelude::*;


const VARTIME_MIN_CHUNK: usize = 1024;
const CT_MIN_CHUNK: usize = 256;

/// Parallel chunked variable-time MSM.
pub fn chunked_vartime_multiscalar_mul(
    scalars: &[Scalar],
    points: &[RistrettoPoint],
) -> RistrettoPoint {
    let n = scalars.len();
    let num_threads = rayon::current_num_threads();

    if n <= VARTIME_MIN_CHUNK || num_threads <= 1 {
        return RistrettoPoint::vartime_multiscalar_mul(scalars, points);
    }

    let chunk_size = ((n + num_threads - 1) / num_threads).max(VARTIME_MIN_CHUNK);

    scalars
        .par_chunks(chunk_size)
        .zip(points.par_chunks(chunk_size))
        .map(|(sc, pt)| RistrettoPoint::vartime_multiscalar_mul(sc, pt))
        .reduce(|| RistrettoPoint::identity(), |a, b| a + b)
}

/// Parallel chunked variable-time optional MSM with lazy decompression.
pub(crate) fn chunked_optional_multiscalar_mul(
    scalars: &[Scalar],
    compressed_points: &[CompressedRistretto],
) -> Option<RistrettoPoint> {
    let n = scalars.len();
    debug_assert_eq!(n, compressed_points.len());
    let num_threads = rayon::current_num_threads();

    if n <= VARTIME_MIN_CHUNK || num_threads <= 1 {
        return RistrettoPoint::optional_multiscalar_mul(
            scalars.iter(),
            compressed_points.iter().map(|c| c.decompress()),
        );
    }

    let chunk_size = ((n + num_threads - 1) / num_threads).max(VARTIME_MIN_CHUNK);

    scalars
        .par_chunks(chunk_size)
        .zip(compressed_points.par_chunks(chunk_size))
        .map(|(sc, pts)| {
            RistrettoPoint::optional_multiscalar_mul(
                sc.iter(),
                pts.iter().map(|c| c.decompress()),
            )
        })
        .reduce(
            || Some(RistrettoPoint::identity()),
            |a, b| match (a, b) {
                (Some(pa), Some(pb)) => Some(pa + pb),
                _ => None,
            },
        )
}

/// Parallel chunked constant-time MSM (Pippenger).
pub(crate) fn chunked_multiscalar_mul(
    scalars: &[Scalar],
    points: &[RistrettoPoint],
) -> RistrettoPoint {
    let n = scalars.len();
    let num_threads = rayon::current_num_threads();

    if n <= CT_MIN_CHUNK || num_threads <= 1 {
        return RistrettoPoint::multiscalar_mul(scalars, points);
    }

    let chunk_size = ((n + num_threads - 1) / num_threads).max(CT_MIN_CHUNK);

    scalars
        .par_chunks(chunk_size)
        .zip(points.par_chunks(chunk_size))
        .map(|(sc, pt)| RistrettoPoint::multiscalar_mul(sc, pt))
        .reduce(|| RistrettoPoint::identity(), |a, b| a + b)
}
