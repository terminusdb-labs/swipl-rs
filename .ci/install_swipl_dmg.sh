#!/bin/bash
HASH='c1b34dea44950af9c1c2e413e8f86cf16bbbd15b43b3098617a48a7f85841dd4'
SWIPL_DMG_NAME='swipl-8.2.4-1.x86_64'
SWIPL_DMG="$SWIPL_DMG_NAME.dmg"
echo "$HASH  $SWIPL_DMG" > checksum

curl "https://www.swi-prolog.org/download/stable/bin/$SWIPL_DMG" > "$SWIPL_DMG"
shasum -a 256 -c checksum
sudo hdiutil attach "$SWIPL_DMG"
cp -rf /Volumes/"$SWIPL_DMG_NAME"/*.app /Applications
