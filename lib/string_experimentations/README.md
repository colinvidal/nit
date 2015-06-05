This project is a collection of modules used to experiment on different variations of Text and its subclasses.
This is only temporary as these modules will eventually be merged into standard library or discarded for those bringing no real improvements to the language.

The modules contained here are :

 * utf8: A draft of implementation of UTF-8 as internal encoding for Strings with automatic indexing.
 * utf8_no_index: Another draft of implementation of UTF-8, this time without indexing.

TODO :

 * utf8:
  * Support for the whole API of Text
  * Any kind of normalization form for equality (NFC probably)
  * Compatibility versions of equality test
  * Locale support
  * Comparisons
  * to_upper/lower fully-compatible with Unicode

 * utf8_no_index:
  * Add cache for the last indexed character - DONE
  * Two-way iteration - DONE
  * Intelligent indexed access (calculating the nearest point of insertion, i.e. begin, end, or cache) - DONE
  * UnicodeChar as universal type
  * UnicodeChar => Char and Char => Byte
