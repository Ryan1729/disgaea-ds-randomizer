# Reverse Engineering Notes

## Items

Reversing the items table apparently made it impossible to obtain items at all. Trying to open the buy menu in the shop only resulted in an error sound effect. The bag and warehouse were accessible but empty.

It was hypothesized that leaving the last item in place may have different behaviour. This was disproven.

Reversing only the fists through staves was also attempted, (making the first item the Omni Staff.) This allowed opening the buy menu for the Battle Depot, but not the Weapon Shop.

Reversing only the fists, (making the first item the Ultimus,) allowed opening the buy menu for the Weapon Shop, but no fists were available.

Reversing only the swords, (placing the Yoshitsuna right after the Ultimus) allowed opening the buy menu for the Weapon Shop, and fists were available, but swords were not.

Setting the rank for all the fists through staves to 1 was attempted. No apparent difference was observed in the starting shop.

Setting the rank for all the fists through staves to 40 was also attempted. This made all the relevant items in the Weapon Shop become Legend rarity.

Swapping the rank for just the first two of fists through staves was tried. No apparent difference was observed in the shop.

Swapping the entire first two of fists through staves, (so fists goes Rock Fist, then Wristband) seemed to make the Wristband never show up, but the Rock Fist showed up a lot, and the Common Sword and Common Spear (rank 1 items) still showed up. Maybe something is weird with the first (zeroth) element of the list?

Hypothesis A: The items for the shop, at product rank 0, may be selected from the first 3 items in each available category.
Hypothesis B: There might be a flag or whatever, separate from rank, on some items that prevents them from being sold in the shop.
Hypothesis B_1: The flag or whatever is set on at least the highest few ranked items. That is rank 40, 39, 38, and perhaps more.

Given Hypotheses A, B, and B_1 are true, then that could explain why reversing the list caused the shop to be inaccessible. We would expect that the first few entries were checked for sellable items, but none were found, so no itmes were considered available.

A test for the combined hypotheses A, B, and B_1 would be to reverse the 2nd rank and above fists through staves, leaving the first rank one alone. We expect that only the first rank items, (Wristband, Common Sword, etc.) would be available and the others would not be.

The above test was carried out, and the results were as predicted!

Some information online says that, depending on product rank, the shop can sell items of up to rank 38. This apparently conflicts with Hypotheses B, and B_1.

Hypothesis C: Of the items that are checked for the shop, those above a given rank are filtered out as well.
Hypothesis C_1: The rank 40 items could be special and have another aspect that makes them not be available in the shop too.

Given Hypotheses A, C, and C_1 are true, then we would expect that making the first 3 elements of the list be the rank 1, then rank 10, then rank 40 items, for fists through staves, and simultaneously setting the ranks of those items to rank 1, 2 and 3 respectively, would result in  would result in the rank 1 and rank 10 times being available but not the rank 40 one. (So for fists, that's Wristband, and Cross Counter but no Ultimus.)

The outcome of the above test was only the rank 1 items showing up. This seems to contradict Hypotheses C, and C_1.

So, it may be the case that the online information about rank affecting what can show up in the shop is wrong, or at best incomplete. It seems worthwhile to look for some other piece of information, like a flag, to indicate whether an item can be sold.

Before embarking on investigating specific differences between differently ranked items, it may be worth performing this test to try and disprove Hypothesis A: Copy the rank 1 fist to staves items over the rank 2 and 3 ones, changing the description slightly, so that we can see which get picked up. (There's an implicit hypothesis that the description is not involved in the logic anywhere, but this would be very surprising if it were false!)

This test produced the interesting result that different description-numbered items showed up, but seemingly only one number per weapon type ever showed up!

This suggests that maybe the items are being deduped somehow, and in particular somehow that doesn't preverse ordering. Maybe by hashing the name? This suggests another test of giving all the fist to staves items the name of the corresponding ultimate weapon. We'd expect this would remove all the items from being considered if the names were important, and do nothing but display different names otherwise.

Surprisingly, what happened was that there was no apparent change from vanilla! That is, the items were available but the names did _not_ all get changed to the ultimate weapon! This suggests the names are pulled from the large block of names elsewhere in the ROM instead of from the item table when displaying them!

To test that hypothesis about the text being displayed from elsewhere we can overwrite some of that text with the ultimate weapon name as well.

Performing that test by adding code to overwrite the other instance of the string "Wristband\0" with "Ultimus\0" resulted in the display updating as expected.

At this point, it seems like understanding more of the pieces of the item table would be useful, since whay appears in the shop seems more complicated than expected.

Many of the stats were identifiable by comparing numbers to online tables. The values being in the same order as things are displayed in game certainly helped!

One value was monotonically increasing for each item, with gaps that often were at or near round decimal values. This suggests that the values were designed to be added to over time and perhaps moved around as items got added. It seemed plausible that this was the sort key for items. To try and disprove this hypothesis the values were replaced with 65535 minus the original value. This turned out to cause the store to not allow buying anything, similarly to when things were reversed. So the next thing that was tried was reversing the whole list of items and sorting the counting up values. This caused the items at the end of the list to show up in the store! That is the stats, descriptions, and icons of the items were what one would expect given the list is reversed, (Gency's Exit at the top, etc.). They were also priced in a way that seemed to fit . And the displayed names were still for the usual items (Wristband, Rock Fist, ...). It seems to make sense to call these counting up values hte sort key now.

