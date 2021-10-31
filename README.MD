# Run the TLA tool from command line
install tla-bin from https://github.com/pmer/tla-bin, which helps wrap tla tool for command line

# Evaluate the specification directly without cfg file
tlc <spec file> -continue
example command to spec SyncChannel.tla
tlc SyncChannel.tla -tool -modelcheck -coverage 1 -config ./SyncChannel.cfg -deadlock
the following command helps to dump all sates into a text file
tlc SyncChannel.tla -tool -modelcheck -coverage 1 -config ./SyncChannel.cfg -deadlock -dump SyncChannel.dot

the following command dumps out dot file for the graph. the dot file can be visualized as an image
note that the dot after the -dump tells tlc the dumped format is in dot
tlc DieHard.tla  -config DieHard.cfg -dump dot Diehard.dot -tool -modelcheck

# Config file for TLA+ model
a TLA+ models needs a config file to run.
the following are all the possible options for the config file
	* INVARIANT
	* INVARIANTS
	
	* PROPERTY
	* PROPERTIES
	
	* CONSTANT
	* CONSTANTS
	
	* CONSTRAINT
	* CONSTRAINTS
	
	* ACTION_CONSTRAINT
	* ACTION_CONSTRAINTS
	
	* INIT
	* NEXT
	* VIEW
	* SYMMETRY
	* TYPE
	* TYPE_CONSTRAINT
    * CHECK_DEADLOCK (TRUE/FALSE)
