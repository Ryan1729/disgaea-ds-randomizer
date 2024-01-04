# Reverse Engineering Notes

## Items

Reversing the items table apparently made it impossible to obtain items at all. Trying to open the buy menu in the shop only resulted in an error sound effect. The bag and warehouse were accessible but empty.

It was hypothesized that leaving the last item in place may have different behaviour. This was disproven.

Reversing only the fists through staves was also attempted, (making the first item the Omni Staff.) This allowed opening the buy menu for the Battle Depot, but not the Weapon Shop.

Reversing only the fists, (making the first item the Ultimus,) allowed opening the buy menu for the Weapon Shop, but no fists were available.

Reversing only the swords, (placing the Yoshitsuna right after the Ultimus) allowed opening the buy menu for the Weapon Shop, and fists were available, but swords were not.

Setting the rank for all the fists through staves to 1 was attempted. No apparent difference was observed in the starting shop.

Setting the rank for all the fists through staves to 40 was also attempted. This made all the relevant items in the Weapon Shop become Legend rarity.
