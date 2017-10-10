'''
Pytest module:

Call using ```pytest test_all```
'''
import os
from os.path import dirname, realpath

class TestAwsFpgaAll:
    '''
    Pytest test class.
    
    NOTE: Cannot have an __init__ method.
    '''
    
    def setup_class(self):
        '''
        Do any setup required for tests.
        '''
        self.test_dir = dirname(realpath(__file__))
        return
    
    def test_md_links(self):
        rc = os.system(self.test_dir + "/check_md_links.py")
        assert rc == 0
        