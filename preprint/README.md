# LAA preprint

This directory contains a self-contained submission build of
**“Permanental Dominance for Generalized Matrix Functions of Order Four”**
for *Linear Algebra and its Applications* (LAA).

The directory organization follows the useful separation in
[jinshanmu/CrouzeixConjecture](https://github.com/jinshanmu/CrouzeixConjecture/tree/main/preprint),
but the journal formatting is deliberately different: LAA is an Elsevier
journal, so this version uses the official `elsarticle` preprint class and
the numerical `elsarticle-num` bibliography style.

## Files

- `permanental_dominance_n4.tex` — LAA/Elsevier manuscript.
- `references.bib` — BibTeX database for all cited literature.
- `permanental_dominance_n4.bbl` — generated bibliography for portable
  submission and arXiv packaging.
- `permanental_dominance_n4.pdf` — compiled preprint.
- `highlights.txt` — four submission highlights, each within Elsevier's
  85-character limit.
- `elsarticle.cls`, `elsarticle-num.bst` — Elsevier template files,
  vendored so the directory compiles independently.
- `.gitignore` — ignores transient LaTeX build files while retaining the
  PDF and generated `.bbl`.

## Build

Run from this directory:

```bash
latexmk -pdf permanental_dominance_n4.tex
```

To remove transient build products:

```bash
latexmk -c permanental_dominance_n4.tex
```

## Author metadata

The front matter identifies Siwei Zeng as an independent researcher and uses
`endlesslethe@gmail.com` as the corresponding-author email.

Elsevier Editorial Manager expects the submitted LaTeX source files at one
folder level. Upload the contents of this directory together rather than
uploading a nested directory tree.

The class and bibliography style are from the official
[STM Document Engineering `elsarticle` repository](https://github.com/STM-Document-Engineering/elsarticle)
(version 3.4c, 2025-01-11), distributed under the LPPL as stated in the files.
