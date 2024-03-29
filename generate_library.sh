#! /bin/sh

# Create folder with leanpkg.toml with two dependencies.
mkdir -p combined_lib
cp leanpkg.toml combined_lib/
cd combined_lib/
sed -i 's/name.*/name = "combined_lib"/g' leanpkg.toml
sed -i '/path/d' leanpkg.toml

# Get last revision of code:
LAST_COMMIT=$(git ls-remote https://github.com/ferrandf/valenceformula.git HEAD | cut -f1)
echo "valenceformula = {git = \"https://github.com/ferrandf/valenceformula\", rev = \"$LAST_COMMIT\"}" >> leanpkg.toml

leanproject get-mathlib-cache || true

# Generate a zip in dist/library.zip
        
cd ..
./lean-web-editor/mk_library.py -i combined_lib | python ./lean-web-editor/detect_errors.py
