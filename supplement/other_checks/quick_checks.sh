#!/bin/bash
# Re-runs the quick checks (M1 iso/descriptions, M2/M3 stars, M5 sets). Needs ./vc built and vp.py.
cd "$(dirname "$0")"
date
echo "== M1: tight-max lists, C vs Python, and the third reviewer's G?bffG"
./vc iso 'G?Ox|o' 'G?Ky\c'; ./vc iso 'G?bffG' 'G?Ky\c'; ./vc iso 'G?bffG' 'G@CZ\W'; ./vc iso 'G@CZ\W' 'G?Ky\c'
python3 -I vp.py canon 'G?Ox|o' 'G?Ky\c' 'G?bffG' 'G@CZ\W' | awk '{print "py canon hash", $1, $2}'
echo "== M1: descriptions (built by vp.py) GNz_OG = K33+bc, pendants at e,f; GNzc?_ = K33+bc, pendants at a,d; E}GO = diamond+2 pendants"
./vc iso 'GNz_OG' 'G@CZ\W'; ./vc iso 'GNzc?_' 'G?Ky\c'; ./vc iso 'E}GO' 'E^Q?'
python3 -I vp.py canon 'GNz_OG' 'G@CZ\W' 'GNzc?_' 'G?Ky\c' 'E}GO' 'E^Q?' | awk '{print "py canon hash", $1, $2}'
./vc g6 'G?Ky\c' 'G@CZ\W' 'G?bffG' 'E^Q?'; python3 -I vp.py g6 'G?Ky\c' 'G@CZ\W' 'G?bffG' 'E^Q?'
echo "== M2/M3: K_{1,6} = FsaC?, K_{1,4} = Ds_"
./vc g6 'FsaC?' 'Ds_'; python3 -I vp.py g6 'FsaC?' 'Ds_'
echo "== M2: C and Python lists of other-reading violators matched by isomorphism"
./vc match c_oth7.g6 p_oth7.g6; ./vc match c_oth8.g6 p_oth8.g6
echo "== M5: sets in K?CXX\NVz^P~"
./vc set 'K?CXX\NVz^P~' "0 1 2 3 11"; ./vc set 'K?CXX\NVz^P~' "1 2 3 11"; ./vc sets4with 'K?CXX\NVz^P~' 4 0
date
