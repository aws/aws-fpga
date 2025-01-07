from enchant.tokenize import Filter

class HexFilter(Filter):
    def _skip(self, word):
        if word.startswith(("0x", "0X")):
            try:
                int(word[2:], 16)
                return True
            except ValueError:
                return False
        elif word.startswith(("x", "X")):
            try:
                int(word[1:], 16)
                return True
            except ValueError:
                return False
        return False