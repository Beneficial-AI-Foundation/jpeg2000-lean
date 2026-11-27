# jpeg2000-lean
A Formally Verified jpeg2000 decoder

## What "formally verified" means

The decoder is written in Lean 4, and the Lean kernel checks proofs that, for **every**
input:

* it never crashes, reads out of bounds or loops forever, and its memory use and output
  size stay within the `Limits` you pass;
* it computes the same image as a line-by-line transcription of the JPEG 2000 standard
  (ITU-T T.800): exactly for lossless images, within a stated error bound for lossy ones;
* decoding the project's reference encoder's lossless output returns the original image.

Agreement with OpenJPEG, the official conformance images and real PDF images, along with
colour management, speed and fuzzing, is **tested** rather than proved. See
[docs/verification.md](docs/verification.md) for what is proved, what is tested, the known
limitations and what you have to trust.

The [consumer API](docs/api.md) describes the pinned Lean dependency, image
channels, opacity and limits used by the safe-pdf integration.

## License

MIT — see [LICENSE](LICENSE). The conformance and corpus files are not part of this repository: they are fetched by SHA-256 under their own terms (see `docs/corpus.md`).
