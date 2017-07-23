##################################################
### URAM options - 2017.1 sdx
##################################################
switch $uram_option {
    "2" {
        set synth_uram_option "-max_uram_cascade_height 2"
        set uramHeight 2
    }
    "3" {
        set synth_uram_option "-max_uram_cascade_height 3"
        set uramHeight 3
    }
    "4" {
        set synth_uram_option "-max_uram_cascade_height 1"
        set uramHeight 4
    }
    default {
        set synth_uram_option "-max_uram_cascade_height 1"
        set uramHeight 4
    }
}