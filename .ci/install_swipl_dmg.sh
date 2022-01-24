#!/bin/bash
HASH='51815bd2c614f53df4c1a53d8e5b5f16bbfb4f670a1fdf5b1fefcc0f473d5cd0'
SWIPL_DMG_NAME='swipl-8.4.1-1.x86_64'
SWIPL_DMG="$SWIPL_DMG_NAME.dmg"
echo "$HASH  $SWIPL_DMG" > checksum

curl "https://www.swi-prolog.org/download/stable/bin/$SWIPL_DMG" > "$SWIPL_DMG"
shasum -a 256 -c checksum
sudo hdiutil attach "$SWIPL_DMG"
cp -rf /Volumes/"$SWIPL_DMG_NAME"/*.app /Applications
