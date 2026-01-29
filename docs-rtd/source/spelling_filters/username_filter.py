from enchant.tokenize import Filter


class UsernameFilter(Filter):
    def _skip(self, word) -> bool:
        """Skip word if it starts or ends with '@'"""
        if word.startswith("@") or word.endswith("@"):
            return True
        return False
