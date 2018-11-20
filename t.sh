#/bin/bash

echo	'CM.make "sources.cm";
	Tester.testAdd();
	Tester.testSub();
	Tester.testMul();' | sml;
