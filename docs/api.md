# Decoder API for PDF consumers

The initial safe-pdf integration uses commit `9a8880a8604dbebf93b99253e7965d54673dc534`
with Lean 4.36.0. The `libraryOnly` setting omits development targets so a consumer
can declare its own `Tests.*` modules. Add this declaration to the consumer's Lake file and run
`lake update jpeg2000`. Commit the generated manifest alongside the declaration.

```lean
require jpeg2000 from git
  "https://github.com/Beneficial-AI-Foundation/jpeg2000-lean.git" @
  "9a8880a8604dbebf93b99253e7965d54673dc534"
  with NameMap.empty.insert `libraryOnly "true"
```

```lean
import JPEG2000.Image

def displayBytes (limits : JPEG2000.Limits) (bytes : ByteArray) :
    Except JPEG2000.Error (Nat × Nat × ByteArray) := do
  let image ← JPEG2000.decode limits bytes
  let pixels ← image.interleaved8 limits
  return (image.width, image.height, pixels)
```

`bytes` is the JP2 or raw codestream after preceding PDF filters have run.
The example returns the image's colour channels in pixel order. Read
`image.space` and `image.channels.size` to interpret that buffer. An RGB
image produces three bytes per pixel. Other spaces can produce different counts.

* **Precision and colour.** Each `Channel` has a depth, signedness and an exact
  `get?` sample reader. Use those samples for PDF Indexed lookup. The interleavers
  rescale to their output depth. A PDF Indexed palette can require the original
  indices (`applyPalette := false`). Options also control sYCC inference and
  conversion. Resolve the PDF colour space before choosing these options.
  Embedded ICC bytes are available in `image.iccProfile` for the consumer.
* **Opacity.** `image.smaskInData mode` selects the embedded opacity channel
  for modes 1 and 2 and reports whether the colours are premultiplied.
  `interleaved8` omits alpha by default. Passing `true` appends an available
  alpha channel. PDF masking and compositing take place in the consumer.
* **Geometry.** At reduction zero, `width` and `height` describe the original
  image area. At other reductions they describe the output on the reduced
  reference grid. Check the PDF dictionary against the original SIZ geometry
  in `image.decoded.header.siz`. The output retains its grid origin.
* **Limits and failures.** Pass explicit limits to both decoding and interleaving.
  `maxImageArea` applies to the declared full image. `maxWorkSamples` and
  `maxDecodedBytes` bound the reduced work planes and sample buffers at their
  respective checks. The caller accounts for its own pixmap and page allocations.
  Preserve the typed `Except` result until the renderer decides how to report a failure.

For native component grids, use `JPEG2000.decodeCodestream` or read
`image.decoded.comps`. For 16-bit output, `image.interleaved16 limits`
produces big-endian samples. The resource contracts and the PDF fixture catalog
are described in [resources.md](resources.md) and [corpus.md](corpus.md).
