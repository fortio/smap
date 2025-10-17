[![Go Reference](https://pkg.go.dev/badge/fortio.org/smap.svg)](https://pkg.go.dev/fortio.org/smap)
[![Go Report Card](https://goreportcard.com/badge/fortio.org/smap)](https://goreportcard.com/report/fortio.org/smap)
[![GitHub Release](https://img.shields.io/github/release/fortio/smap.svg?style=flat)](https://github.com/fortio/smap/releases/)
[![Coverage](https://codecov.io/github/fortio/smap/branch/main/graph/badge.svg?token=LONYZDFQ7C)](https://codecov.io/github/fortio/smap)

# smap
Concurrent Safe Generic golang map with optionally sorted iteration (provides go1.24 iterators).
Zero dependencies.

See https://pkg.go.dev/fortio.org/smap

## History
This was originally developed for [fortio.org/tsync](https://github.com/fortio/tsync#tsync) which uses and battle tests it including for race conditions (there aren't any!).
