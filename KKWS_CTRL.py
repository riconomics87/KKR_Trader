import subprocess
import sys
import os
import re
import pickle
import time
import shared_memory_dict
import ast
import signal

signal.signal(signal.SIGINT, signal.SIG_IGN)
PID = [1,2]
#import KKWS_POS_MNGR

#print(KKWS_POS_MNGR.main("1 TUE 15 0.025565 1"))
systemd_stat = None
class SharedDict:
    def __init__(self, name, process_id):

        filename = "controller.txt" 
        file_path = "/root/" + filename if os.name == 'posix' else filename

        # Validate process_id (1 or 2 for Peterson's algorithm)
        if process_id not in [1, 2]:
            raise ValueError("process_id must be 1 or 2")

        # Initialize shared memory dictionary
        self.shared_dict = shared_memory_dict.SharedMemoryDict(name=name, size=1048576)
        self.file_path = file_path 
        self.id = process_id
        self.name = name
        self.last_update_by_id = -1
        
        # Set up synchronization variables for Peterson's algorithm
        self.shared_dict.setdefault('flag1', False)
        self.shared_dict.setdefault('flag2', False)
        self.shared_dict.setdefault('turn', self.id)

        if self.shared_dict.get('command') != {}:
            self._load_from_file()
            self._save_to_file()
        else:
            self.shared_dict['command'] = (None, None)

    def _acquire_lock(self):
        # Peterson's algorithm for mutual exclusion
        other_id = 3 - self.id
        self.shared_dict['flag' + str(self.id)] = True
        self.shared_dict['turn'] = other_id
        while (self.shared_dict['flag' + str(other_id)] and 
               self.shared_dict['turn'] == other_id):
            pass

    def _release_lock(self):
        self.shared_dict['flag' + str(self.id)] = False

    def _load_from_file(self):
        # Load dictionary from file if it exists
        try:
            with open(self.file_path, 'r') as f:
                lines = f.readlines()
                self._acquire_lock()
                try:
                    for line in lines:
                        key, value = line.strip().split(':', 1)  # Split on first colon
                        self.shared_dict[key] = ast.literal_eval(value)#value
                finally:
                    self._release_lock()
        except FileNotFoundError:
            pass  # File doesn't exist yet, start with empty dict

    def _save_to_file(self):
        # Save dictionary to file
        if self.file_path:
            self._acquire_lock()
            try:
                with open(self.file_path, 'w') as f:
                    for key, value in self.shared_dict.items():
                        # Skip synchronization keys
                        if key not in ['flag1', 'flag2', 'turn']:
                            f.write(f"{key}:{value}\n")
            finally:
                self._release_lock()

    def view(self):
        self._acquire_lock()
        try:
            return self.shared_dict
        finally:
            self._release_lock()

    def read(self, key, default=None):
        self._acquire_lock()
        try:
            self.shared_dict = shared_memory_dict.SharedMemoryDict(name=self.name, size=1048576)
            return self.shared_dict.get(key, default)  
        finally:
            self._release_lock()

    def write(self, key, value, pid = None):
        self._acquire_lock()
        try:
            #if (pid == None and self.id != self.last_update_by_id) or (pid != None):
            self.last_update_by_id = self.id
            self.shared_dict[key] = value
            self._save_to_file()
        finally:
            self._release_lock()

    def cleanup(self):
        # Save to file before unlinking
        self._save_to_file()
        # Release shared memory
        self.shared_dict.unlink()

system_controller = SharedDict(name='system_controller', process_id=2)

def controller_display():
    global selector, statdef, current_command, current_status 
    os.system('clear' if os.name == 'posix' else 'cls')
    print(f"Kraken Daily Relative Strength Controls")
    print("="*51)
    print(f"1 {selector[0]} Run   | {statdef[0]}")
    print(f"2 {selector[1]} Pause | {statdef[1]}")
    print(f"3 {selector[2]} Stop  | {statdef[2]}")
    print("="*51)

def main_menu():
    global selector, statdef, current_command, current_status  
    while True: 
        runstat = system_controller.view()
        #print(system_controller.last_update_by_id,runstat, runstat['command'][0] == None)
        statdef = [[f"{runstat['command'][1]}", '', ''],['', f"{runstat['command'][1]}", ''],['', '', f"{runstat['command'][1]}"]][{"Run":0, "Pause":1, "Stop":2}[runstat['command'][0]]]
        os.system('clear' if os.name == 'posix' else 'cls')
        selector = [[">"," "," "],[" ",">"," "],[" "," ",">"]][{"Run":0, "Pause":1, "Stop":2}[runstat['command'][0]]]
        if statdef in [['', '', ''],['Running', '', ''],['', 'Paused', ''],['', '', 'Stopped']]:
            controller_display()
            choice = input("Choose an option (1-3) or press CTRL + Z to exit: ").strip()

            if choice == '1' and runstat['command'][1] != 'Running':
                statdef = ["Starting","",""]
                system_controller.write('command', ('Run','Starting'), 1)
            elif choice == '2' and runstat['command'][1] not in ['Paused','Stopped']:               
                statdef = ["","Pausing",""]
                system_controller.write('command', ('Pause','Pausing'))
            elif choice == '3' and (runstat['command'][1] != 'Stopped' or runstat['command'][1] == 'Running'):
                statdef = ["","","Stopping"]
                system_controller.write('command', ('Stop','Stopping'))
if __name__ == "__main__":
    main_menu()
    #system_controller.cleanup()


