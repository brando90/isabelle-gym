import console
from console import IsabelleConsole

c = IsabelleConsole()
c.use_thy('../mp1_test')
for each in c.get_goals():
    print(each)

c.process.kill()