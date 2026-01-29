import re
from enchant.tokenize import Filter


class RTLHexFilter(Filter):
    def _skip(self, word) -> bool:
        if "'h" not in word:
            return False

        if "_" not in word:
            return True

        # Check if segments after underscores are valid 4-digit hex
        for match in re.finditer("_", word):
            segment = word[match.start() + 1 : match.start() + 5]
            if len(segment) < 4 or not all(c in "0123456789abcdefABCDEF" for c in segment):
                return False
        return True
