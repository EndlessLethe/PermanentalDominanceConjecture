# ELA preprint

This directory contains a self-contained submission build of
**“The General Subgroup Permanental-Dominance Conjecture in Order Four”**
for *The Electronic Journal of Linear Algebra* (ELA).

The directory organization follows the useful separation in
[jinshanmu/CrouzeixConjecture](https://github.com/jinshanmu/CrouzeixConjecture/tree/main/preprint),
but the journal formatting follows ELA's official sample and its required
SIAM LaTeX2e macros.

## Files

- `permanental_dominance_n4.tex` — ELA manuscript.
- `references.bib` — BibTeX database for all cited literature.
- `permanental_dominance_n4.bbl` — generated bibliography for portable
  submission and arXiv packaging.
- `permanental_dominance_n4.pdf` — compiled preprint.
- `cover_letter.tex`, `cover_letter.pdf` — one-page ELA cover letter and its
  editable source.
- `siamart1116.cls`, `siamplain.bst` — the class and bibliography style from
  the SIAM macros package linked by ELA, vendored so the journal-specific
  files are available locally.
- `.gitignore` — ignores transient LaTeX build files while retaining the
  PDF and generated `.bbl`.

## Build

Run from this directory:

```bash
latexmk -pdf permanental_dominance_n4.tex
latexmk -pdf cover_letter.tex
```

A standard TeX distribution with the `algorithms` package is required by
`siamart1116.cls`, even though this manuscript does not use algorithms.

To remove transient build products:

```bash
latexmk -c permanental_dominance_n4.tex
```

## Author metadata

The front matter identifies Siwei Zeng as an independent researcher and uses
`endlesslethe@gmail.com` as the corresponding-author email. The author's ORCID
is [`0009-0008-8914-7143`](https://orcid.org/0009-0008-8914-7143).

The abstract is written in the third person and is below ELA's 250-word
limit. The front matter contains six keywords and the 2020 Mathematics
Subject Classification codes `15A15`, `15B57`, and `20C15`. Theorem and
equation numbering follow the official ELA sample.

The template files are from the official
[ELA template package](https://journals.uwyo.edu/index.php/ela/about/submissions)
and remain subject to the LaTeX Project Public License stated in those files.
