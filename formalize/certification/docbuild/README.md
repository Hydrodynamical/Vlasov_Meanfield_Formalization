# docbuild — doc-gen4 API documentation for the Vlasov package

A sibling package (same pattern as `../blueprint-demo`) that builds the
doc-gen4 HTML documentation for `Vlasov` and its full import closure
(all of Mathlib — doc-gen4 has no external-linking mode, so hyperlink
self-containedness forces rendering the closure).

The built site is **1.2 GB** (59 MB gzipped), so it is not in git. It ships
as the `docs-v1` release asset, which `.github/workflows/pages.yml` downloads
and serves under `/docs` on the GitHub Pages site. That URL is what the
blueprint's declaration buttons target
(`…/docs/find/#doc/<name>`, configured as `\dochome` in
`../blueprint-demo/blueprint/src/web.tex`).

## Rebuild

```bash
cd formalize/certification/docbuild
lake build Vlasov:docs        # output: .lake/build/doc/  (~2.5 h, ~25k jobs)
```

On a machine with the main package already built, reuse its caches by
symlinking the shared dependencies before the first build (this is how
`blueprint-demo` builds in minutes rather than hours):

```bash
mkdir -p .lake/packages
for p in Cli LeanSearchClient Qq aesop batteries importGraph mathlib plausible proofwidgets; do
  ln -sf "$(pwd)/../../../Vlasov/.lake/packages/$p" .lake/packages/$p
done
```

From a clean clone without the symlinks, `lake build` fetches the pinned
dependencies per `lake-manifest.json`; Mathlib's post-update hook pulls the
olean cache (`lake exe cache get`), so nothing recompiles from scratch.

**Two traps, both hit and fixed on 2026-07-08:**

1. **Require order.** doc-gen4 pins different revisions of shared packages
   (`Cli`, `plausible`, …) than Mathlib does. The `Vlasov` require must come
   LAST in `lakefile.toml` so Mathlib's pins win; otherwise the resolver
   mismatches and `lake update` fails.
2. **`lake update` reaches through the symlinks.** With the symlink layout
   above, a resolution that picks a different rev will `git checkout` inside
   the SHARED checkout under `Vlasov/.lake/packages/`, silently moving the
   main package's dependency and invalidating its warm build. Avoid
   `lake update` here; if you must run it, verify afterwards that the shared
   checkouts still match `Vlasov/lake-manifest.json` and restore any that
   moved (`git -C ../../../Vlasov/.lake/packages/<p> checkout <rev>`).

## Publish

```bash
cd .lake/build && tar czf vlasov-docs-v4.29.1.tar.gz doc
gh release upload docs-v1 vlasov-docs-v4.29.1.tar.gz --clobber
gh workflow run pages.yml    # redeploys the composed site
```
