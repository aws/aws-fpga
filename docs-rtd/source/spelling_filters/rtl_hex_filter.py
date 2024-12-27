import enchant
import re
from enchant.tokenize import Filter

class RTLHexFilter(Filter):
    def _skip(self, word):
        rtl_hex_literal_prefix = "’h"
        if rtl_hex_literal_prefix in word:
            # If the literal makes use of underscores for readability
            if  "_" in word:
                underscore_positions = [pos.start() for pos in re.finditer("_", word)]
                for pos in underscore_positions:
                    aligned_word = ""
                    try:
                        aligned_word = word[pos + 1 : pos + 5]
                        word_len = len(aligned_word)
                        if word_len < 4:
                            raise IndexError(f"Word {aligned_word} is only {word_len} hex digits long!")
                        try:
                            int(aligned_word, base=16)
                            return True
                        except ValueError as v:
                            print("ERROR: Could not convert hex word literal {aligned_word} to a base-16 integer!")
                            return False
                    except IndexError as i:
                        print(f"ERROR: Could not gather 4 hex digits after underscore: \n\t{aligned_word} \n\t{word}")
                        print((i))
                        return False
            else:
                return True
        return False
