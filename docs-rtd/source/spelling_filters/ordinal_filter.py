import enchant
from enchant.tokenize import Filter

class OrdinalFilter(Filter):
    def _skip(self, word):
        is_ordinal = any([word.endswith(suffix) for suffix in ("st", "nd", "rd", "th")])
        if not is_ordinal:
            return False
        try:
            number = int(word[:-2])
            if number % 10 == 1 and number % 100 != 11:
                return word.endswith('st')
            elif number % 10 == 2 and number % 100 != 12:
                return word.endswith('nd')
            elif number % 10 == 3 and number % 100 != 13:
                return word.endswith('rd')
            else:
                return word.endswith('th')
        except ValueError:
            return False