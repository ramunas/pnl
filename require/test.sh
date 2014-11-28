#!/bin/bash

cat <<END | poly
use "require.ML";
Uses.setLoadPaths ["/Users/ramunasgutkovas/Projects/symbolic/pwb-pnl-sos"];
Uses.uses "pwb/workbench";
END

