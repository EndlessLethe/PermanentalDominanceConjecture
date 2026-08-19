#!/bin/sh
set -eu

lake build
lake env lean AxiomAudit.lean
