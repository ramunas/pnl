#!/bin/sh

set -e
echo "PolyML.export(\"pnl\", NomTerm.test);\n" | pwb sml -i @nom-terms.ML
gcc -o pnl pnl.o -Wl,-no_pie -L/brew/lib/ `pkg-config --cflags --libs polyml`

