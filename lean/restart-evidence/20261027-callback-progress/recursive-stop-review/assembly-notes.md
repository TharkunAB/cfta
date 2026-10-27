# Evidence assembly correction

The first local metadata validation assumed the two new Audit imports were prepended. The exact source places them in the import list. That local assertion failed before any seal or final validation was written. The corrected validation removes only those two literal, unique import lines and recovers the entire old Audit bytes. No proof, compiler result, source, or documented claim changed.
