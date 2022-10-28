#!/bin/bash
HASH='abe28eeb98b8bc89721812ea96fccf984a877a830dda58f291e6e2213ae07a9a'
SWIPL_DMG_NAME='swipl-8.4.3-1.fat'
SWIPL_DMG="$SWIPL_DMG_NAME.dmg"
echo "$HASH  $SWIPL_DMG" > checksum

curl "https://www.swi-prolog.org/download/stable/bin/$SWIPL_DMG" > "$SWIPL_DMG"
shasum -a 256 -c checksum
sudo hdiutil attach "$SWIPL_DMG"
cp -rf /Volumes/"$SWIPL_DMG_NAME"/*.app /Applications
