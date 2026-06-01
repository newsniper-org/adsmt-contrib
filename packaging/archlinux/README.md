# Arch Linux packaging — adsmt-contrib

Three PKGBUILDs covering the source-only delivery of adsmt-contrib's
Rocq + Isabelle emit backends across all three release channels.

## Why source-only

Both `adsmt-emit-rocq` and `adsmt-emit-isabelle` are pure `lib`
crates — no `[[bin]]` targets. They are consumed by downstream Rust
code (typically as a `cargo` git-rev pin or a workspace path dep),
not invoked as system binaries. No file goes under `/usr/bin/`.

A source-only package therefore captures the natural delivery shape:
ship the workspace tree under `/usr/src/adsmt-contrib/` and let the
rebuilder pick features / vendor / patch as needed.

## Matrix

| channel  | PKGBUILD                              | source                  | pkgver shape |
|----------|---------------------------------------|-------------------------|---|
| stable   | `adsmt-contrib-src/`                  | `v1.0.0` tag tarball    | `1.0.0` |
| testing  | `adsmt-contrib-src-testing/`          | `testing` git branch    | `1.0.0.rc.r<count>.<sha>` |
| git      | `adsmt-contrib-src-git/`              | `main` git branch       | `1.0.0.dev.r<count>.<sha>` |

All three packages install identical contents (full workspace tree
under `/usr/src/adsmt-contrib/`) — they only differ in source rev
and pkgver shape. Three pkgbases mutually conflict so only one is
installed at a time.

## Build instructions

```bash
cd packaging/archlinux/adsmt-contrib-src
makepkg --syncdeps --noconfirm
```

(`stable` PKGBUILD requires the upstream `v1.0.0` tag to be cut on
adsmt-contrib's main branch; testing/git PKGBUILDs pull from current
branch state.)

## Status (2026-06-01)

makepkg testing deferred until adsmt main v1.0.0 stable cut commits
— see `memory/v1_0_0_scope_expansion.md` in the adsmt main repo.

## Relationship to adsmt main

This packaging is **independent** of adsmt main's 9-PKGBUILD
matrix at `~/AD1/packaging/archlinux/`. The two repos have their own
release cadences (per the bidirectional embed decision, P5 option 5).
adsmt main's `adsmt-src` split ships the adsmt workspace; this
ships the adsmt-contrib workspace. Consumers wanting both source
trees install both packages.
