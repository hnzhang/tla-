# Run the TLA tool from command line
install tla-bin from https://github.com/pmer/tla-bin, which helps wrap tla tool for command line

# Evaluate the specification directly without cfg file
tlc <spec file> -continue

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