from gym import Gym
import os
import json 


def isar_tactic_ast(line, gym):
    isar_ast = gym.console.get_isar_ast(line)
    # TODO: get the tactic ast.
    return isar_ast 

def get_tactic_goal_pair(line, gym):
    tactic = isar_tactic_ast(line, gym)
    return tactic, gym.console.goals

def get_data(isar_code_stream):
    gym = Gym()
    data = []
    for line in isar_code_stream:
        line = line.strip()
        if line.strip().startswith("by") or line.strip().startswith("with") or line.strip().startswith("apply"): # tentative measure to decide which lines to include.
            data.append(get_tactic_goal_pair(line, gym))
        gym.process_line(line)
    return data


def open_isar_file(path, thy_filename, verbose=False):
    with open(path) as f:
        isar_code = f
        out_dir = './data/'
        out_filename = thy_filename + '_data.json'
        if not os.path.exists(out_dir):
            try:
                os.makedirs(out_dir)
            except OSError as e:
                print('[ERROR] error while creating output directory.'+ out_dir +' \n')
                raise
        with open(out_dir+out_filename, "w+") as out:
            data = get_data(isar_code)
            out.write(json.dumps(data))