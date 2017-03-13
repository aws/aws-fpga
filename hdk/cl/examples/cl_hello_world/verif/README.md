# Hello World CL Example Simulation

The cl_hello_world example includes a basic test that exercises the Hello World Register as well as the Virtual LED Register. The test writes a value to the Hello World Register and then reads it back. Additionally, it reads the Virtual LED register.

The test can be run from the [verif/scripts] (scripts) directory with one of three different simulators:

```
    $ make TEST=test_hello_world
    $ make TEST=test_hello_world VCS=1
    $ make TEST=test_hello_world QUESTA=1
```

Note that the appropriate simulators must be installed.

