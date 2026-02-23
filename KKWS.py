from cmath import inf
import requests
import orjson
import urllib
import hashlib
import hmac
import base64
import time
from sortedcontainers import SortedList
import traceback
import asyncio
import websockets
import pandas as pd
import numpy as np
from collections import deque, defaultdict
from datetime import datetime, timedelta, timezone
import pytz
import pickle
import os 
import sys
from filelock import FileLock, Timeout
import aiofiles
from decimal import Decimal, ROUND_FLOOR, ROUND_CEILING

from typing import Dict, Optional, List, Any, Callable, Awaitable
from contextlib import asynccontextmanager
from enum import Enum

import shared_memory_dict
import ast

from array import array

from aiorwlock import RWLock
from dataclasses import dataclass

from pathlib import Path

import functools
import inspect
import math
pd.set_option('future.no_silent_downcasting', True)
script_name = os.path.basename(__file__).split('.')[0]

TEST_MODE = {1:True, 2:False}[2]
ACTIVATE = True

tf = (
      ('minute',     60, 'M'),
      ('hourly',   3600, 'H'),
      ('daily',   86400, 'D'),     
      ('weekly', 604800, 'W')    
     )[2]
quota = {1:1.15, 2:1.075}[1]
timeframe = tf[2]
log_header = (
                f"KRAKEN PERFORMANCE TRADE LOGS		TIMEFRAME : {tf[2]}",
                 " "  
             )

system_log_header = (
                      f"KRAKEN PERFORMANCE SYSTEM LOGS     TIMEFRAME : {tf[2]}",
                       " " 
                    )

interval_identifier = tf[2]
ws_public = None
ws_private = None

instrument_dict    = {}
#balance_dict       = {}
liquid_pairs       = []
balance_checked    = False
ohlc_subscriptions = set()
slots_to_trade     = 10
slots_to_display   = 10
diversify_by       = 10
exit_type = {1:"trail", 2:"lead", 3:None}[1]
usd_balance = 0
session_balance = 0
tf_divisor = {'M':60,'H':168,'D':7}[tf[2]]
target_weekly_percentage = {'t':10, 'q':4, 'h':2, 'w':1}
order_switch = {"b":"buy", "s":"sell"}

last_current_hour = -1

H24_Vol = 0#500_000     
candlesDict        = {}
bookDict           = {}
tradesDict         = {}
tradable           = {}
sec_data_count = 0
stablecoins = ['USDT', 'USDC', 'AUD', 'EUR', 'GBP', 'JPY', 'CAD', 'USDQ', 'USDR', 'DAI', 'USDS', 'PYUSD', 'PAXG', 'TUSD', 'USDD', 'RLUSD', 'USDG', 'UST', 'USD1']
prev_df = pd.DataFrame()
pairs_with_upward_movement = set()
movementType = 'S2S'
interval = None    #{'rM' : 60, 'rH' : 3600, 'r24H' : 86400, 'rW' : 604800, 'default' : None }
rrcnt = interval or tf[1]
spike_pct_entry = 0
#slot_map = {s : [None,None] for s in range(0, slots_to_trade)}
session_watchlist = [] 
last_type = {'close':'close', 'mid':'mid'}['mid']
sec_running_cnt = {}
prevRanks  = np.array([])
#currRanks  = np.array([])
currranks_set = set()
liveRanks  = np.array([])
riskRanks  = []
retRanks   = []
swapLevels = {}
subList = set()
sps = []
rankfiller = np.array(['-','-','-','-','-','-','-','-','-','-'])
mincnt = [0,0,0,0,0,0,0,0,0,0]
control_risk = True
asset_to_tuple = {}
order_manager = {}
volume_weight_type = {1:'LIN', 2:'FIB'}[2]
slot_volume = dict()
public_ws_conn  = -1 
private_ws_conn = -1
system_command = None
swapshift = 1
volume_store = {}
exit_on_swap_pct = False
sort_option = {1: "ret", 2:"inflows", 3:"inflow_weighted_ret"}[2]  
initial_price_option = {1:"open", 2:"low"}[2]
log_position_changes = False
adjusted_sort = {'spread':1,'spread_decline':2}['spread_decline']
#pending_events = []
interval_seconds = 14_400    #24h = 86_400, 7d = 604_800, 1h = 3_600, 4h = 14_400, 1m = 60
interval_minutes = 60
mn = 0
qset = {
        'D1' : (7     ,1),
        'H1' : (24    ,1),
        'H2' : (168   ,1),
        'M1' : (60    ,1),
        'M2' : (1440  ,1),
        'M3' : (10080 ,1)
       }['H2']
quota_pct = ((100 / qset[0]) / 100) + (((100 / qset[0]) / 100) / 100) + 1

def exception_decorator():
    def decorator(func):
        if not ACTIVATE:
            return func
        if inspect.iscoroutinefunction(func):
            @functools.wraps(func)
            async def async_wrapper(*args, **kwargs):
                try:
                    return await func(*args, **kwargs)
                except Exception as e:
                    await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION  ")
                    return None
            return async_wrapper
        else:
            @functools.wraps(func)
            def sync_wrapper(*args, **kwargs):
                try:
                    return func(*args, **kwargs)
                except Exception as e:
                    message = f"{e.__traceback__.tb_lineno} {e}"
                    try:
                        loop = asyncio.get_running_loop()
                        loop.create_task(system_log(message, "EXECUTION  "))
                    except RuntimeError:
                        asyncio.run(system_log(message, "EXECUTION  "))
                    return None
            return sync_wrapper
    return decorator

class SystemStatusManager:
    def __init__(self):
        self._system_status = "offline"
        self._lock = asyncio.Lock()

    async def get_status(self):
        """Asynchronously read the system status."""
        async with self._lock:
            return self._system_status

    async def set_status(self, new_status: str):
        """Asynchronously update the system status."""
        async with self._lock:
            self._system_status = new_status

system_status = SystemStatusManager()

class Balances:
    def __init__(self):
        self.checked      = False
        self.liquid_pairs = []
        self.usd          = 0
        self.session      = 0
        self.starting_session = 0
        self.records      = {}
        self.lock         = asyncio.Lock()

    async def update(self, key, value):
        async with self.lock:
            setattr(self, key, value)

    async def get(self, key):
        async with self.lock:
            return getattr(self, key.split('/')[0])

    async def update_records(self, key, value):
        async with self.lock:
            self.records[key] = value

    async def delete_record(self, key):
        async with self.lock:
            del self.records[key]

    async def append_to_liquid_pairs(self, value):
        async with self.lock:
            self.liquid_pairs.append(value)

    async def remove_from_liquid_pairs(self, value):
        async with self.lock:
            self.liquid_pairs.remove(value)

    async def set_starting_session(self, value):
        async with self.lock:
            if self.starting_session == 0:
                self.starting_session = value 
    '''
    def quota_met(self):
        if self.starting_session != 0:
            return self.usd_balance > int(self.starting_session * quota)
        return False
    '''
balances = Balances()

class Executions:
    def __init__(self):
        self.last_execution      = None
        self.last_buy_execution  = None
        self.last_sell_execution = None
        self.opened_trade        = False
        self.session_executions  = {}
'''
class RollingRateLimiter:
    def __init__(self, max_requests, window_seconds):
        self.max_requests = max_requests
        self.window_seconds = window_seconds
        self.requests = []  # Store request timestamps
        self.lock = asyncio.Lock()  # Ensure safe concurrent access

    async def limit(self):
        async with self.lock:  # Ensure thread-safe access
            now = time.monotonic()

            # Remove expired timestamps (older than the rolling window)
            self.requests = [t for t in self.requests if t > now - self.window_seconds]

            if len(self.requests) >= self.max_requests:
                # Calculate sleep time until the oldest request expires
                sleep_time = self.requests[0] + self.window_seconds - now
                await asyncio.sleep(sleep_time)

            # Record the current request timestamp
            self.requests.append(time.monotonic())
'''
class LockManager:
    def __init__(self):
        self.locks: Dict[str, asyncio.Lock] = {}

    def get_lock(self, var_name: str) -> asyncio.Lock:
        """Get or create a lock for a specific global variable."""
        if var_name not in self.locks:
            self.locks[var_name] = asyncio.Lock()
        return self.locks[var_name]

    def has_active_lock(self, var_name: str) -> bool:
        """
        Return True if a lock exists for var_name and is currently acquired.
        """
        lock = self.locks.get(var_name)
        return lock.locked() if lock is not None else False

    @asynccontextmanager
    async def acquire(self, var_name: str):
        """Context manager to acquire and release a lock for a variable."""
        lock = self.get_lock(var_name)
        await lock.acquire()
        try:
            yield
        finally:
            lock.release()

# Instantiate LockManager globally
lock_manager = LockManager()

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
        self.shared_dict.setdefault('turn', 1)

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
               time.sleep(0)

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
                        self.shared_dict[key] = ast.literal_eval(value)
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

controller_link = SharedDict(name='system_controller', process_id=1)

#@exception_decorator()
async def controller():
    global system_command, current_system_state
    system_command, current_system_state = controller_link.read('command')
    if current_system_state == 'Running':
        if system_command == 'Stop':
            order_state_list = await osd.get_all_order_state_list() #order_state_dict["buy_pending".value] + order_state_dict["sell_allowed".value] + order_state_dict["sell_allowed".value]
            print('order_state_list',order_state_list)
            if not order_state_list:
                controller_link.write('command', ('Stop', 'Stopped'))
                sys.exit(0)
            else:
                controller_link.write('command', ('Stop', 'Stopping'))
        elif system_command == 'Pause':
            controller_link.write('command', ('Pause', 'Paused'))
            return
    elif current_system_state == 'Paused':
        if system_command == 'Stop':
            controller_link.write('command', ('Stop', 'Stopped'))
            sys.exit(0)
        elif system_command == 'Run':
            controller_link.write('command', ('Run', 'Starting'))
            return
        elif system_command == 'Pause':
            return
    elif current_system_state == 'Stopped':
        controller_link.write('command', ('Run', 'Starting'))
        return
    elif current_system_state == 'Starting':
        controller_link.write('command', ('Run', 'Running'))
    elif current_system_state == 'Stopping':
        order_state_list = await osd.get_all_order_state_list() #order_state_dict["buy_pending".value] + order_state_dict["sell_allowed".value] + order_state_dict["sell_allowed".value]
        print('order_state_list',order_state_list)
        if not order_state_list:
            controller_link.write('command', ('Stop', 'Stopped'))
            system_command, current_system_state = controller_link.read('command')
            sys.exit(0)
    elif current_system_state == 'Pausing':
        controller_link.write('command', ('Pause', 'Paused'))

class SmartRateLimiter:
    """
    Unified Kraken WS v2 rate limiter (2025 version)
    
    Use:
    - account_for_take_profit=True  → protects space for future take-profit (+1 send +8 cancel)
    - account_for_take_profit=False → only protects entry + stop-loss trigger (minimal reserve)
    """
    __slots__ = ("buf", "thr", "cnt", "pend", "protect_tp")

    def __init__(
        self,
        safety_buffer: int = 8,
        tier_threshold: int = 125,               # 60 Starter / 125 Intermediate / 180 Pro
        account_for_take_profit: bool = True     # main toggle
    ):
        self.buf = safety_buffer
        self.thr = tier_threshold
        self.protect_tp = account_for_take_profit
        self.cnt: dict[str, float] = {}          # symbol → current ratecount
        self.pend: dict[str, dict] = {}          # symbol → {"main": id, "tp": id} (optional)

    async def feed(self, msg: dict):
        """Feed every executions message"""
        for item in msg.get("data", []):
            if (rc := item.get("ratecount")) is not None:
                sym = item.get("symbol")
                if sym:
                    self.cnt[sym] = float(rc)

    async def register_entry(self, symbol: str, main_order_id: str):
        self.pend[symbol] = {"main": main_order_id, "tp": None}

    async def register_tp(self, symbol: str, tp_order_id: str):
        if symbol in self.pend:
            self.pend[symbol]["tp"] = tp_order_id

    async def close_trade(self, symbol: str):
        self.pend.pop(symbol, None)
   
    async def submit(
        self,
        symbol: str,
        send_func: Callable[..., Awaitable[Any]],
        order_data: dict,
        is_take_profit: bool = False
    ) -> bool:
        """
        Main method to submit orders safely.
        
        Returns True if order was sent successfully, False if blocked by rate limit.
        """
        # Decide how much headroom we reserve
        if is_take_profit:
            headroom = 9                     # +1 send +8 cancel
        elif self.protect_tp:
            headroom = 12                    # entry + stop trigger + future TP + cancel
        else:
            headroom = 3                     # minimal: entry + stop trigger + small buffer

        current = self.cnt.get(symbol, 0.0)
        if current + headroom > self.thr - self.buf:
            print(f"[RateLimit BLOCKED] {symbol} | count={current:.2f} | need={headroom}")
            return False

        # Safe to send
        try:
            response = await send_func(order_data)
            
            # Try to extract order_id (Kraken formats vary)
            order_id = (
                response.get("result", {}).get("order_id") or
                response.get("order_id") or
                response.get("data", [{}])[0].get("order_id")
            )

            if order_id:
                if is_take_profit:
                    await self.register_tp(symbol, order_id)
                else:
                    await self.register_entry(symbol, order_id)

            return True

        except Exception as e:
            print(f"[RateLimit] Send failed for {symbol}: {e}")  # will retry these orders if still buy signal
            return False

limiter = SmartRateLimiter(safety_buffer=15, tier_threshold=125)  # Intermediate

class OrderStateDict: 
    def __init__(self):
        self.order_state_dict = {'buy_pending': [], 'sell_allowed': [], 'sell_pending': [], 'hold': []}    #len(osd.order_state_dict['sell_allowed'])
        self.lock             = asyncio.Lock()

    async def order_state_dict_update(self, key, value):
        async with self.lock:
            self.order_state_dict[key].append(value) 

    async def order_state_dict_remove(self, key, value):
        async with self.lock:
            try:
                self.order_state_dict[key].remove(value)
            except (KeyError, ValueError):
                pass

    async def get_order_state_list(self, key):
        async with self.lock:
            return self.order_state_dict[key]

    async def get_order_state_set(self, key):
        async with self.lock:
            return set(self.order_state_dict[key])

    async def get_all_order_state_list(self):
        async with self.lock:
            return self.order_state_dict['buy_pending'] + self.order_state_dict['sell_allowed'] + self.order_state_dict['sell_pending']

    async def get_sell_allowed(self):
        async with self.lock:
            return self.order_state_dict['sell_allowed']

    async def get_buy_pending(self):
        async with self.lock:
            return self.order_state_dict['buy_pending']

    async def get_hold(self):
        async with self.lock:
            return self.order_state_dict['hold']

osd = OrderStateDict()  #await osd.order_state_dict_update(self.state, self.asset)

#NOTUSED
class FillState(Enum):
    TAKE_PROFIT  = 'takeprofit'
    STOP_LOSS    = 'stoploss'
    MARKET_ENTRY = 'marketentry'
    MARKET_EXIT  = 'marketexit'
    FLAT         = 'flat'

class OrderTypeReqID(Enum):
    MKT_ID    = 100001
    MKT_W_SL  = 100002
    TP_ID     = 100003
    CANCEL_TP = 100004
    CANCEL_ON_DISCONNECT = 100005

#print(OrderTypeReqID.ADD_ORDER.value)

class OrderManager:
    '''
    __slots__ = (
            'asset',
            'state',
            'laststate',
            'fillstate',
            'lastfillstate',
            'slot',
            'lastslot',
            'allotment_id',
            'current_order_id',
            'current_order_future',
            'lock',
            #'orders',
            'spikepct',
            'swappct',
            'slots_per_period',
            'take_profit_price',
            'take_profit_order_id',
            'stop_loss_price',
            'stop_loss_order_id',
            'avg_fill_price',
            'execution',
            'entry_by',
            'exit_by',
            'pnl_pct',
            'tp',
            'weighted_allocation',
            'allotment_number',
            'current_position_risk',
            'entry_ask',
            'exit_bid',
            'tp_hit',
            '_orders',
    )
    '''
    def __init__(self, asset):
        self.asset = asset
        self.state                = 'idle'
        self.laststate            = 'idle'
        self.fillstate            = FillState.FLAT
        self.lastfillstate        = FillState.FLAT
        self.slot                 = -1
        self.lastslot             = -1
        self.allotment_id         = -1
        self.current_order_id     = None
        self.current_order_future = None
        self.lock                 = asyncio.Lock()
        #self.orders               = []
        self.spikepct             = 0
        self.swappct              = 0 
        self.slots_per_period     = 0

        #Current Order Information
        self.take_profit_price    = 0
        self.take_profit_order_id = 0
        self.stop_loss_price      = 0
        self.stop_loss_order_id   = 0
        self.avg_fill_price       = 0

        self.execution            = {}

        self.entry_by        = 0
        self.exit_by         = 0

        self.entry_ask = 0 #<<<<REMOVE
        self.exit_bid = 0 #<<<<REMOVE
        self.pnl_pct = 0
        self.tp = 0
        self.weighted_allocation = 0
        self.current_position_risk = None
        self._orders: set[str] = set()
        self.allotment_id = -1
        self.moved_to_breakeven = False
        self.pos_qty = 0

    def order_ack(self, msg: dict) -> None:
        if msg.get("success"):
            self._orders.add(msg.get("order_id"))
            
    def ack_check(self, exec_: dict, order_confirmation: str = True) -> bool: #ack_check(entry, False)
        orders = self._orders
        oid = exec_.get("order_id")
        if oid in orders:
            if order_confirmation:
                orders.discard(oid)   # one-time confirm, shrinks future work
            return True
        return False

    async def submit_order(self, order_action):
        try:
            # ---- Phase 1: decide + reserve under lock (NO awaits) ----
            async with self.lock:

                # BUY path
                if self.state == "idle" and order_action[0] == "buy":
                    #fut = asyncio.get_running_loop().create_future()
                    #self.current_order_future = fut
                    self.state = "buy_pending"
                    asset = self.asset
                    #allotment_id = self.allotment_id  # capture for rollback use
                    do = "buy"
                # SELL path
                elif self.state == "sell_allowed" and order_action[0] == "sell":
                    fut = asyncio.get_running_loop().create_future()
                    self.current_order_future = fut
                    # transition locally; external osd updates later
                    prev_state = self.state
                    self.state = "sell_pending"
                    asset = self.asset
                    do = "sell"
                    # capture what you need
                elif self.state == "sell_allowed" and order_action[0] in {"update_stop", "update_take_profit"}:
                    # if you truly do nothing async here, you can just return
                    return self.current_order_future
                else:
                    return None  # or raise if you prefer

            # ---- Phase 2: do awaits OUTSIDE lock ----
            if do == "buy":
                await osd.order_state_dict_update("buy_pending", asset)
                await self.market_buy_order_w_stop_loss()
                
                '''
                if order_response is None:
                    # rollback external state first (outside lock)
                    await osd.order_state_dict_remove("buy_pending", asset)
                    #await allocator.release_allotment(allotment_id)

                    # rollback internal state under lock
                    async with self.lock:

                        await osd.order_state_dict_remove(self.state, self.asset)
                        await allocator.release_allotment(self.allotment_id) 
                     
                        self.state = "idle"
                        self.pos_qty = 0
                        self.entry_by = 0
                        self.allotment_id = -1

                    return

                # success: commit under lock
                async with self.lock:
                    # state likely stays buy_pending until ack/fill logic changes it
                    self.order_ack(order_response)
                return 
                '''
            elif do == "sell":
                # You removed sell_allowed externally; do that outside lock
                await osd.order_state_dict_remove("sell_allowed", asset)
                await osd.order_state_dict_update("sell_pending", asset)

                await self.market_sell_order()
                return 

        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}", "EXECUTION  ")
            # Optional: if you want, fail the current future safely
            try:
                async with self.lock:
                    fut = getattr(self, "current_order_future", None)
                    if fut is not None and not fut.done():
                        fut.set_exception(e)
            except Exception:
                pass
            return None
    
    async def execution_response2(self, response):
        try:
            async with self.lock:
                if self.state == "buy_pending": 
                    if response['order_status'] in {'partially_filled', 'filled'}:# and not self.current_order_future.done(): 
                        q = response["last_qty"]          # <-- use this
                        if response["side"] == "buy":
                            self.pos_qty += q                        

                        #slot_map[self.slot][0] = self.asset
                        self.current_order_future.set_result(response)
                        response.update({"entry_by":self.entry_by})
                        self.execution.update(response)
                        if self.state != None: 
                            await osd.order_state_dict_remove(self.state, self.asset)
                        self.state = "sell_allowed"
                        await osd.order_state_dict_update(self.state, self.asset)
                        #print(self.asset, self.state,self.slot, slot_map, response) #test
                        
                    else:
                        self.state = "idle"
                        self.current_order_future.set_exception(Exception(response.get('error', 'Order not filled'))) # <
                elif self.state == "sell_pending":
                    if response['order_status'] in {'partially_filled', 'filled'} and not self.current_order_future.done():
                        self.current_order_future.set_result(response)

                        await osd.order_state_dict_remove(self.state, self.asset)
                        await system_log(f"RELEASING ALLOTMENT ID {self.allotment_id}","ORDER SELL 2")
                        await allocator.release_allotment(self.allotment_id) 
                        self.execution.clear()
                        self.laststate = self.state                        
                        self.state = "idle"
                        self.pos_qty = 0
                        self.entry_by = 0
                    else: # <
                        self.state = "sell_allowed" 
                        self.current_order_future.set_exception(Exception(response.get('error', 'Order not filled'))) # <
                else:
                    pass
                self.current_order_future = None # <
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION  ")

    async def execution_response(self, response):
        try:
            # ---------- Phase 1: internal state transition (NO awaits) ----------
            do_osd_remove = None
            do_osd_update = None
            do_release_allotment = False
            do_log_release = False

            async with self.lock:
                fut = self.current_order_future

                if self.state == "buy_pending":
                    if response.get("order_status") in {"partially_filled", "filled"}:
                        if response.get("side") == "buy":
                            self.pos_qty += response.get("last_qty", 0)

                        if fut and not fut.done():
                            fut.set_result(response)

                        response.update({"entry_by": self.entry_by})
                        self.execution.update(response)

                        do_osd_remove = self.state
                        self.state = "sell_allowed"
                        do_osd_update = self.state

                    else:
                        self.state = "idle"
                        if fut and not fut.done():
                            fut.set_exception(
                                Exception(response.get("error", "Order not filled"))
                            )

                elif self.state == "sell_pending":
                    if response.get("order_status") in {"partially_filled", "filled"}:
                        if fut and not fut.done():
                            fut.set_result(response)

                        do_osd_remove = self.state
                        do_release_allotment = True
                        do_log_release = True

                        self.execution.clear()
                        self.laststate = self.state
                        self.state = "idle"
                        self.pos_qty = 0

                    else:
                        self.state = "sell_allowed"
                        if fut and not fut.done():
                            fut.set_exception(
                                Exception(response.get("error", "Order not filled"))
                            )

                self.current_order_future = None

                asset = self.asset
                allotment_id = self.allotment_id

            # ---------- Phase 2: external side effects (OUTSIDE lock) ----------
            if do_osd_remove:
                await osd.order_state_dict_remove(do_osd_remove, asset)

            if do_osd_update:
                await osd.order_state_dict_update(do_osd_update, asset)

            if do_log_release:
                await system_log(
                    f"RELEASING ALLOTMENT ID {allotment_id}",
                    "ORDER SELL 2"
                )

            if do_release_allotment:
                await allocator.release_allotment(allotment_id)

        except Exception as e:
            await system_log(
                f"{e.__traceback__.tb_lineno} {e}",
                "EXECUTION  "
            )
    
    '''
    async def get_quota(self, fill_price):
        equity_pct = equitylogger.equity_pct
        quotapct = 1.0001 #1.01 #1.0001
        return (quotapct + -equity_pct) * fill_price['data'][0]['avg_price'], fill_price['data'][0]['avg_price']
    '''
    async def get_state(self):
        async with self.lock:
            return self.state

    async def get_slot(self):
        async with self.lock:
            return self.slot  

    async def set_state(self, state):
        async with self.lock:
            self.state = state

    async def set_slot(self, slot):
        async with self.lock:
            self.slot = slot 

    def reset(self, asset):
        return self.__init__(asset)

    async def cancel_order(self, order_id_list):
        ws_token = private_ws.pri_ws_token
        order_data = {
                        "method": "cancel_order",
                        "params": {
                                    "order_id": [*order_id_list],
                                    "token"   : ws_token
                                  },
                     }
        #remove
        #await send_message(private_ws.ws, order_data)
    
    async def market_sell_order(self, req_id = 3):
        try:
            ws_token = private_ws.pri_ws_token
            instrument_info = instrument_dict[self.asset]
            #pair_balance = await balances.get(self.asset)
            #last_qty = float(self.execution['last_qty'])
            pos_qty = self.precision_normalization(self.pos_qty, instrument_info['qty_precision'])
            order_data = {  
                            "method" : "add_order",
                            "params": {
                                        "order_type" : "market",  
                                        "side"       : "sell",        
                                        "order_qty"  : pos_qty, 
                                        "symbol"     : self.asset,
                                        "token"      : ws_token
                                      },
                            "req_id": req_id * 10 + self.allotment_id
                         }      
            await system_log(order_data, "ORDER SELL   ")
            return await private_ws.send(order_data)
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION  ")

    async def move_to_breakeven(self):
        if not self.moved_to_breakeven:
            ws_token = private_ws.pri_ws_token
            order_data = {
                            "method": "amend_order",
                            "params": {
                                         "cl_ord_id": "",
                                         "triggers": {
                                                         "price": ""
                                                     },
                                         "token": ws_token
                                      }
                         }
            await system_log(order_data, "ORDER SELL   ")
            response = await send_message(private_ws.ws, order_data)
            if response.get("success"):
                self.moved_to_breakeven = True
            

        pass
    '''
    async def market_buy_order(self): 
        self.allotment_id, allocation = await allocator.lock_allotment()# session_balance / 10 #await allocator.lock_allotment(self.slot)
        if allocation == 0:
            return        
        if allocation > 2:
            ask = candlesDict[self.asset].ask
            order_data = {
                            "method": "add_order",
                            "params": {
                                        "order_type" : "market",  
                                        "side"       : "buy",        
                                        "order_qty"  : f"{allocation / ask}",  #float(order_qty),  #progressive_order_qty / candlesDict[self.asset].bid
                                        "symbol"     : self.asset,
                                        "token"      : ws_token
                                      },
                         }

            #await send_message(private_ws.ws, order_data)
        else:
            await allocator.release_allotment(self.allotment_id)
    '''
    async def market_buy_order_w_stop_loss(self, req_id = 1): 
        try:
            ws_token = private_ws.pri_ws_token
            await system_log("1", f"ORDER BUY  1")
            self.allotment_id, allocation = await allocator.lock_allotment(self.asset)# session_balance / 10 #await allocator.lock_allotment(self.slot)            
            if allocation == 0:
                await allocator.release_allotment(self.allotment_id)
                await osd.order_state_dict_remove(self.state, self.asset)
                await system_log(f"2.1 allocation is 0, allotment {self.allotment_id} being released", f"ORDER BUY  2")
                self.allotment_id = -1
                self.entry_by = 0
                return {}
            await system_log(f"2.2 allocation is {allocation}, allotment {self.allotment_id} being locked", f"ORDER BUY  2")
            base_units, quote_units = await self.calculate_order_qty(allocation)
            stop_loss_pct = candlesDict[self.asset].stop_pct(self.entry_by) * 100
            await system_log(f"base {base_units} quote {quote_units} allocation {allocation} allotment_id {self.allotment_id} {await allocator.is_alloted(self.allotment_id)}", f"ORDER BUY  3")
            instrument_info = instrument_dict[self.asset]
            stop_loss_pct = self.precision_normalization(stop_loss_pct, 2) #instrument_info['price_precision']
            base_units_normalized = self.precision_normalization(base_units, instrument_info['qty_precision'])
            if base_units_normalized > instrument_info["qty_min"]:
                await system_log("4", f"ORDER BUY  4")
                order_data = {
                                "method": "add_order",
                                "params": {
                                            "order_type"    : "market",  
                                            "side"          : "buy",        
                                            "order_qty"     : base_units_normalized,  #float(order_qty),  #progressive_order_qty / candlesDict[self.asset].bid
                                            "symbol"        : self.asset,
                                            "token"         : ws_token,
                                            "conditional":  {
                                                              "order_type"         : "stop-loss",            #stop-loss-limit
                                                              "trigger_price_type" : "pct",
                                                              "trigger_price"      : -stop_loss_pct
                                                            },                                       
                                          },
                                "req_id": req_id * 10 + self.allotment_id
                             }
                await system_log(order_data, "ORDER BUY	 5")
                return await private_ws.send(order_data)
            else:
                await allocator.release_allotment(self.allotment_id)
                await osd.order_state_dict_remove(self.state, self.asset)
                await system_log("2.1 allocation is 0", f"ORDER BUY  2")
                self.allotment_id = -1
                self.entry_by = 0
                return None
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION  ")

    async def market_buy_order_w_trailing_stop_loss(self, req_id = 2): 
        ws_token = private_ws.pri_ws_token
        self.allotment_id, allocation = await allocator.lock_allotment(self.asset)# session_balance / 10 #await allocator.lock_allotment(self.slot)
        if allocation == 0:
            return
        base_units, quote_units = await self.calculate_order_qty(allocation)
        base_units_normalized = self.qty_normalization(base_units)
        stop_loss_pct = candlesDict[self.asset].stop_dist
        if base_units > instrument_dict[self.asset]["qty_min"]:
            order_data = {
                            "method": "add_order",
                            "params": {
                                        "order_type"    : "market",  
                                        "side"          : "buy",        
                                        "order_qty"     : f"{base_units_normalized}",  #float(order_qty),  #progressive_order_qty / candlesDict[self.asset].bid
                                        "symbol"        : self.asset,
                                        "token"         : ws_token,
                                        "time_in_force" : "IOC",
                                        "conditional": {
                                                         "order_type"         : "trailing-loss",            #stop-loss-limit
                                                         "trigger_price_type" : "pct",
                                                         "trigger_price"      : stop_loss_pct,
                                                         "reference"          : "index"
                                                       },                                        
                                      },
                            "req_id": req_id * 10 + self.allotment_id
                         }

            #await send_message(private_ws.ws, order_data)
            
            if await limiter.submit(self.asset, private_ws.w, order_data, is_take_profit=False):
                print("Entry submitted safely")
            else:
                print("Entry blocked — protecting take-profit headroom")
        else:
            await allocator.release_allotment(self.slot)
            await osd.order_state_dict_remove(self.state, self.asset)
            self.entry_by = 0

    async def place_take_profit(self, filled_qty: float, tp_pct_above: float, req_id: int = 4) -> dict:
        ws_token = private_ws.pri_ws_token
        tp_price = 0
        order_data =  {
                            "method": "add_order",
                            "params": {
                                        "order_type"  : "take-profit",
                                        "side"        : "sell",
                                        "order_qty"   : filled_qty,
                                        "symbol"      : self.asset,
                                        "reduce_only" : True,
                                        "triggers"    : {
                                                        "reference"  : "index",
                                                        "price"      : round(tp_price, 2),
                                                        "price_type" : "static"
                                                        },
                                        "time_in_force" : "gtc",
                                        "token"         : ws_token,
                                        "req_id"        : req_id
                                    }
                        }
        #await send_message(private_ws.ws, order_data)
    #tp_order_id = order_res["result"]["order_id"]
    async def cancel_take_profit(self, tp_order_id: str, token: str, req_id: int = 5) -> dict:
        return {
                    "method" : "cancel_order",
                    "params" : {
                                "order_id" : tp_order_id,
                                "token"    : token,
                                "req_id"   : req_id
                            }
                }

    async def add_execution_entry(self, value):
        async with self.lock:
            self.execution = value
    
    async def get_execution_entry(self, key):
        async with self.lock:
            return self.execution.get(key)
    
    async def remove_execution_entry(self, key):
        async with self.lock:
            if key in self.execution:
                self.execution = {}
  
    async def get_execution(self):
        async with self.lock:
            return self.execution

    async def calculate_order_qty(self, allocation):
        try:
            """
            allows us to only risk a fixed percentage of our allocation per trade.
            stop_loss_distance_percent = d_spread + (max_spread * 2)
            Calculate position sizes.
            - entry_price: Entry price in quote currency (e.g., 100000)
            - stop_loss_distance_percent: Stop-loss distance as percentage of entry (e.g., 2.5 for 2.5%)
            - capital: Your total trading capital in quote currency
            Returns: (base_units, quote_units_committed)
            """
        
            risk_percent = 0.01  # Fixed 1% risk           
            loss_per_unit = candlesDict[self.asset].ask * candlesDict[self.asset].stop_pct(self.entry_by) 
            base_units = (risk_percent * allocation) / loss_per_unit
            quote_units = base_units * candlesDict[self.asset].ask
            return base_units, quote_units
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION   ")
    async def calculate_take_profit_pct(entry_price, stop_loss_distance_percent, capital, target_profit_percent):
        """
        stop_loss_distance_percent = d_spread + (max_spread * 2)
        Calculate the take-profit distance % needed to achieve target_profit_percent of capital.
        Piggybacks on same inputs as position sizing.
        - target_profit_percent: Desired profit as % of capital (e.g., 2 for 2%)
        Returns: take_profit_distance_percent (from entry price)
        """
        risk_percent = 0.01  # Fixed 1% risk
        loss_per_unit = entry_price * stop_loss_distance_percent
        base_units = (risk_percent * capital) / loss_per_unit
    
        target_profit_amount = target_profit_percent * capital
        tp_distance_per_unit = target_profit_amount / base_units
        take_profit_distance_percent = (tp_distance_per_unit / entry_price) 
    
        return take_profit_distance_percent

        # Example: 1% risk, 2.5% SL distance, $100k capital, want 2% profit
        # tp_dist = calculate_take_profit_distance(100000, 2.5, 100000, 2)
        # print(tp_dist)  # Outputs: 5.0 ? Take-profit at 105,000

    def precision_normalization(self,x: float, decimals: int) -> float:
        factor = 10 ** decimals
        return math.floor(x * factor) / factor 

async def calculate_recovery_gain(initial_capital, target_profit_percent, loss_percent):
    current_capital = initial_capital * (1 - loss_percent)
    target_capital = initial_capital * (1 + target_profit_percent)
    required_gain = ((target_capital - current_capital) / current_capital)   
    return required_gain

class Allocator:
    def __init__(self):
        """
        Initialize the Allocator with the total balance divided into equal parts.

        Attributes:
            total_amount (float): The current total balance (initialized from session_balance).
            num_parts (int): Number of diversification parts (from diversify_by).
            part_value (float): Initial value per part (total_amount / num_parts).
            part_balances (dict): Dictionary mapping part indices (0 to num_parts-1) to their balances.
            open_parts (set): Set of part indices that are currently locked (in use).
            available_parts (deque): Deque of available (unlocked) part indices for efficient auto-assignment.
            lock (asyncio.Lock): Lock for synchronizing access to shared state in async operations.
            next_part (int): Not used; deque handles assignment for speed.
        """
        self.total_amount = 0 #balances.usd
        self.num_parts = diversify_by
        self.part_value = self.total_amount / self.num_parts
        self.part_balances = {i: self.part_value for i in range(self.num_parts)}
        self.open_parts = set()
        self.available_parts = deque(range(self.num_parts))
        self.lock = asyncio.Lock()
        self.assets = {i: None for i in range(self.num_parts)}
    
    async def lock_allotment(self, asset):
        """
        Auto-assign and lock an available allotment, update the total amount,
        and return the assigned part_num and its current balance.

        Returns:
            tuple: (part_num, balance) if successfully locked, else (-1, 0).

        Note: Uses deque for O(1) popleft to prioritize speed. Critical section is minimized.
        """
        await self.update_total_amount()
        async with self.lock:
            if not self.available_parts:
                return -1, 0
            part_num = self.available_parts.popleft()
            self.open_parts.add(part_num)
            allotment = self.part_balances[part_num]
        await self.update_total_amount()
        self.assets[part_num] = asset
        return part_num, allotment
   
    async def release_allotment(self, part_num):
        """
        Release a locked allotment, allowing its balance to be redistributed in future updates,
        and update the total amount.

        Args:
            part_num (int): The index of the part to release (0 to num_parts-1).
        """
        async with self.lock:
            if part_num in self.open_parts:
                self.open_parts.remove(part_num)
                self.available_parts.append(part_num)
        await self.update_total_amount()
        self.assets[part_num] = ''

    def allotments(self):
        """
        Return a dictionary of all allotment balances.

        Returns:
            dict: Mapping of part indices to their current balances.
        """
        return self.part_balances

    async def allotment(self, part_num):
        """
        Return the balance for a specific allotment, safely accessed under lock.

        Args:
            part_num (int): The index of the part.

        Returns:
            float: The current balance of the specified part.
        """
        async with self.lock:
            return self.part_balances[part_num]

    async def update_total_amount(self):
        """
        Update the total balance from session_balance and redistribute the available balance
        equally among unlocked (closed) allotments. Locked allotments retain their balances.

        This method prevents redistribution if all parts are locked or if the new total would
        result in negative available balance, reverting to the old total in such cases.
        """
        async with self.lock:
            old_total = self.total_amount
            self.total_amount = balances.USD  # Update to latest external balance

            # Calculate total balance in locked (open) parts
            locked_balance = sum(self.part_balances[part] for part in self.open_parts)

            # Count unlocked (closed) parts
            closed_parts_count = self.num_parts - len(self.open_parts)
            if closed_parts_count == 0:
                self.total_amount = old_total  # Revert if no closed parts
                return

            # Calculate available balance for redistribution
            available_balance = self.total_amount - locked_balance
            if available_balance < 0:
                self.total_amount = old_total  # Revert if insufficient balance
                return

            # Redistribute equally among closed parts
            new_part_value = available_balance / closed_parts_count
            for part_num in range(self.num_parts):
                if part_num not in self.open_parts:
                    self.part_balances[part_num] = new_part_value

    async def available_parts_count(self):
        """
        Return the number of available (unlocked) allotments.

        Returns:
            int: The number of available parts.
        """
        async with self.lock:
            return len(self.available_parts)

    async def is_alloted(self, part_num):  
        #async with self.lock:
        return part_num in self.open_parts
        
    async def get_id_for_asset(self, _id):
        async with self.lock:
            if _id == -1:
                return None
            else:
                return self.assets[_id]


allocator = Allocator()

async def progressive_weight(allocation, progression): #(use_allocation, use_SPP)
    total_weight = diversify_by
    progression = progression if progression < total_weight else total_weight
    return (progression / total_weight) * allocation

#sorted_spikes = SortedList()

'''@dataclass(order=True)
class Asset:
    return_: float
    symbol: str'''

@dataclass(order=True)
class Asset:
    #spread: float
    return_: float
    symbol: str

class AsyncSortedList:
    def __init__(self):
        self._top_n = 100
        self._list = SortedList()  
        self._all_assets = SortedList(key=lambda a: a.symbol)
        #self._spread_list = SortedList(key=lambda a: a.spread)
        self._symbol_to_asset = {}
        self._lock = RWLock()
        self._save_lock = asyncio.Lock()

    async def update2(self, symbol: str, return_: float):
        async with self._lock.writer:
            try:
                # Remove old asset if it exists
                if symbol in self._symbol_to_asset or return_ == 0:
                    old_asset = self._symbol_to_asset[symbol]
                    self._all_assets.discard(old_asset)
                    #self._spread_list.discard(old_asset)
                    self._list.discard(old_asset)
                    if return_ == 0:
                        return

                #asset = Asset(spread=float(spread), return_=float(return_), symbol=symbol)
                asset = Asset(return_=float(return_), symbol=symbol)
                self._symbol_to_asset[symbol] = asset
                self._all_assets.add(asset)
                '''
                # Update __list according to rules
                if self._spread_list:
                    # Top N spread assets, sorted by return descending
                    top_spread_assets = self._spread_list[:self._top_n] 
                    self._list = SortedList(top_spread_assets, key=lambda a: -a.return_)
                else:
                    # No spread assets, all sorted by return descending
                '''
                self._list = SortedList(self._all_assets, key=lambda a: -a.return_)
            except Exception as e:
                _, _, e_tb = sys.exc_info()                                                                 
                await system_log(f"{e_tb.tb_lineno} {symbol}: {e}", "EXCEPTION  ")
    #------------------------------------------------------------------------------------------
    async def update(self, symbol: str, return_: float):
        err: Optional[Exception] = None
        err_line: Optional[int] = None

        async with self._lock.writer:
            try:
                # Remove old asset if present (from all structures)
                old_asset = self._symbol_to_asset.pop(symbol, None)
                if old_asset is not None:
                    self._all_assets.discard(old_asset)
                    # SortedList supports discard; it won't error if missing
                    self._list.discard(old_asset)

                # If return_ == 0, we only needed to remove it
                if return_ == 0:
                    return

                # Add updated asset
                asset = Asset(return_=-float(return_), symbol=symbol)
                self._symbol_to_asset[symbol] = asset
                self._all_assets.add(asset)

                # Incremental update (fast): O(log n) instead of rebuilding O(n log n)
                self._list.add(asset)

            except Exception as e:
                _, _, e_tb = sys.exc_info()
                err = e
                err_line = e_tb.tb_lineno

        # Never await while holding the writer lock
        if err is not None:
            await system_log(f"{err_line} {symbol}: {err}", "EXCEPTION  ")
    #------------------------------------------------------------------------------------------
    async def remove(self, symbol: str):
        async with self._lock.writer:
            if symbol in self._symbol_to_asset:
                asset = self._symbol_to_asset.pop(symbol)
                self._list.discard(asset) #.remove
                self._all_assets.discard(asset)
                #self._spread_list.discard(asset)

    async def snapshot(self) -> list[Asset]:
        async with self._lock.reader:
            return list(self._list)

    async def length(self) -> int:
        async with self._lock.reader:
            return len(self._list)

    def _set_(self):
        return set(self._symbol_to_asset.keys())

    async def clear(self):
        async with self._lock.writer:
            self._list.clear()
            self._symbol_to_asset.clear()

    async def get_symbols(self, n: int) -> list[str]:
        async with self._lock.reader:
            n = min(n, len(self._list))  # Avoid index errors
            return [asset.symbol for asset in self._list[:n]]

    async def get_returns(self, n: int) -> list[float]:
        async with self._lock.reader:
            n = min(n, len(self._list))  # Avoid index errors
            return [asset.return_ for asset in self._list[:n]]

sl = AsyncSortedList()
static_day = -1
async def print_leaderboard():
    #await slot_volume_update()
    try:
        global pri_restart, pub_restart, trd_restart, static_day
        # Initialize separate lists for each data column
        # Populate the lists with data from currRanks

        #async with lock_manager.acquire('leader'):
            #print(currRanks)
        #await asyncio.sleep(0.000001)
        #os.system('clear' if os.name == 'posix' else 'cls')
        
        #async with lock_manager.acquire('leader'):
        #try:
        rank       = []
        pairs      = []
        spikepct   = []
        chgpct     = []
        swppct     = []
        #open_      = []
        #rhigh      = []
        #low        = []
        #close      = []
        #closep      = []
        avgrisk    = []
        spread     = []
        #swaplevels = [] 
        states     = []
        fills      = []
        dstatus    = []
        wstatus    = []
        #pspikepct = []
        #pchgpct   = []
        #vol = []
        #qwaa      = []
        #TP        = []
        #STP       = []
        #epct      = []
        #allocation = []
        #last_duration = []
        #duration_momentum = []
        ticklen = []
        r_shifted = np.zeros_like(retRanks)
        r_shifted[:-swapshift] = retRanks[swapshift:]
        depth = []
        trades = []
        usd_inflow = []
        cond = []
        for i, pair in enumerate(currRanks, start=1):
            if not currRanks:
                os.system('clear' if os.name == 'posix' else 'cls')
                print("Waiting for ranks . . .")
                await asyncio.sleep(0.01)
                continue
            state = order_manager[pair].state
            states.append(state.upper())
            pos = '>' if state == 'sell_allowed' else ""
            rank.append(f"{pos} {i:2d}")   #i
            #spikepct.append(candlesDict[pair].spike_pct)
            #int((candlesDict[pair].max_risk_pct * 100) * 100) / 100 
            if sort_option == 'inflow_weighted_ret':
                chgpct.append(int(candlesDict[pair].change_pct))
            else:
                chgpct.append(int((candlesDict[pair].change_pct * 100) * 100) / 100)       
            #swppct.append(r_shifted[i - 1])
            #vol.append(candlesDict[pair].surge)
            #open_.append(candlesDict[pair].open)      
            #rhigh.append(candlesDict[pair].resettable_high) 
            #low.append(candlesDict[pair].low)        
            #close.append(order_manager[pair].avg_fill_price)     #candlesDict[pair].close
            #closep.append(candlesDict[pair].close)
            pairs.append(pair.split('/')[0])
            #avgrisk.append(int((candlesDict[pair].max_risk_pct * 100) * 100) / 100)  #relative_risk
            #swaplevels.append(swapLevels[pair]) 
            #state = await order_manager[pair].get_state()

            #smap = slot_map.get(i-1," ")
            #smap = sm.slot_map.get(i," ")
            '''
            try:
                slotcandle = await slotcandles.get(i,{'status':'between'}).get_ohlc()
            except:
                slotcandle = {'status':'between'}
            '''
            dstatus.append(candlesDict[pair].dstatus)
            wstatus.append(candlesDict[pair].wstatus)
            #smap = sm.get_slot(i - 1)
            #fills.append(sm if sm != None else " ")
            #spread.append(int((candlesDict[pair].spread_bps * 100) * 100) / 100)
            #fills.append('>' if state == 'sell_allowed' else "  ")
            #TP.append(order_manager[pair].take_profit_price)
            #STP.append(order_manager[pair].stop_loss_price)
            #allocation.append(slot_volume.get(i,0))
            #pspikepct.append(candlesDict[pair].prev_spike_pct) 
            #pchgpct.append(candlesDict[pair].prev_change_pct) 
            #if candlesDict[pair].hitCount != 0:
                #qwaa.append(candlesDict[pair].smma) 
            #else:
                #qwaa.append(0)
            #last_duration.append(candlesDict[pair].last_duration)
            #duration_momentum.append(candlesDict[pair].duration_momentum)
            ticklen.append(str(candlesDict[pair].intervals).split('.')[0])
            #depth.append(bookDict.get(pair,{"2pct_depth_usd":0})["2pct_depth_usd"]) 
            #depth.append(book_ws.orderbooks[pair]['2pct_depth_usd'] if pair in book_ws.orderbooks else 0.0)
            #trades.append(trades_ws.trades_vol_count[pair][1] if pair in trades_ws.trades_vol_count else 0.0)   # 
            usd_inflow.append(str(candlesDict[pair].inflow).split('.')[0])   #  
            cond.append(order_manager[pair].entry_by)
            
        #Create DataFrame with desired column names directly
        ldf = pd.DataFrame({
                                'SLOT'       : rank,
                                #' '          : fills,
                                'ASSET'      : pairs,                          
                                #'SPK%'       : spikepct,  # Using 'Spike %' instead of 'spikepct'
                                #'SWP%'       : swppct,
                                'CHG'       : chgpct,    # Using 'Chg %' instead of 'chgpct'
                                #'%SPRD'      : spread,
                                'INFLOWS'    : usd_inflow,
                                #'VOL%'       : vol,
                                #'Open'       : open_,     # Using 'Open' instead of 'open_'
                                #'rHigh'      : rhigh,     # Using 'High' instead of 'rhigh'
                                #'Low'        : low,       # Using 'Low' instead of 'low'
                                #'Close'      : close,     # Using 'Close' instead of 'close'
                                #'Swap Level' : swaplevels,
                                #'MAX_RISK%'      : avgrisk, 
                                #f'SP{tf[2]}' : mincnt[:len(rank)],
                                #'STATE'      : states,
                                #'Spread'     : spread,
                                #'close'       : closep,
                                #'Fill'       : close,
                                #'TP'         : TP,
                                #'Equity PCT' : epct
                                #'STP'        : STP
                                #'SMMA'       : qwaa
                                #'ALLOCATION' : allocation
                                #'LAST_DURATION' : last_duration,
                                #'DURATION_MOMENTUM' : duration_momentum
                                #'2% DEPTH' : depth,
                                #'TRADES' : trades,
                                'D' : dstatus,
                                'W' : wstatus,
                                'RSECs' : ticklen,
                                'C': cond

                          })
        if sort_option == 'ret':
            ldf = ldf.drop(columns=['INFLOWS'])
        elif sort_option == 'inflow_weighted_ret':
            ldf = ldf.drop(columns=['INFLOWS'])
            ldf = ldf.rename(columns={'CHG':'INFLOW_WTD_CHG'})
        #ldf['ACTIVE'] = ['->' ]     #[('->' if c > o else ' ') for BOOL in zip(df["Close"], df["Open"])]
        if not ldf.empty:  
            os.system('clear' if os.name == 'posix' else 'cls')
            display_date_now = datetime.now(timezone.utc)
            display_date = display_date_now.strftime("%Y-%m-%d %H:%M")
            day = display_date_now.day
            print(display_date, '---------------------------------------------------------------')
            print(current_system_state,'|','INTERVALS:',interval_seconds,'|','SORT:',sort_option.upper())

            #print(current_system_state)#, 'USD BALANCE:', balances.USD)
            if static_day != day:
                static_day = day
                pub_restart = pri_restart = trd_restart = 0
            print(pub_restart, pri_restart, trd_restart)#, bk_restart)
            print(ldf.to_string(index=False))
            #print()
            #print('OPENED TRADES ---------------------------------------------------------------------------------------')
            #print()
            #print(tradeprints)
            #print('prevRanks',list(prevRanks))
            #print('currRanks',list(currRanks))
            #pubcon =  ws_conn.public_ws_conn 
            #pricon = ws_conn.private_ws_conn
            #print(public_ws_conn, private_ws_conn)
            print(ws_status.public, ws_status.private, ws_status.trades)
            #print('----------------------------------------------------------------------------------------------------')
            print(osd.order_state_dict)
            #m = [asset for asset, manager in order_manager.items() if manager.state != "idle"]
            #m1 = [asset for asset, manager in order_manager.items() if manager.slot != -1]
            #print(m)
            #print(m1)
        #except Exception as e:    #await asyncio.sleep(0)
            #currRanks = []
            #prevRanks = []
            #pass
            await asyncio.sleep(0.01)
    except Exception as e:
        _, _, e_tb = sys.exc_info()               
        await system_log(f"{e_tb.tb_lineno} {e}", "EXCEPTION      ")

retranks = []

async def slot_trader():
    global current_timestamp, currRanks, currranks_set, prevRanks, retRanks, retranks, sorted_spikes, sorted_spikes_rr, asset_to_tuple, sorted_avg_risk, swapLevels, mincnt, tradeprints, session_balance, mn, oldest_timestamp, pending_events#, static_timestamp     

    await system_log("Slot Trader", f"STARTING    ")
    opentrade = 0 #for demo test
    while True:#not await ws_conn_dwn(): #await ws_conn_dwn():  
        try:
            print(1)
            await controller()
         
            order_state_list = await osd.get_all_order_state_list()
            if current_system_state == 'Stopping' and not order_state_list:
                return
            print(2)
            rolling_wstatus = None
            rolling_dstatus = None 
            wstatus = None
            dstatus = None  
            cond1 = False
            cond2 = False 
          
            #async with lock_manager.acquire('sort_spikes'):
            #timechk, _ = await check_timestamp_update()
            #if interval_seconds is None and timechk: #interval == None and                     
                #await set_all_to_idle(cls_timestamp)
                #continue

            #assets = await sl.snapshot()  # Safe read
            currRanks = await sl.get_symbols(10)
            retRanks  = await sl.get_returns(10)

            if not currRanks:# or prevRanks.size == 0:
                await asyncio.sleep(0.01)
                continue
            print(3)
            currranks_set = sl._set_() 
            sell_allowed_set = set(await osd.get_sell_allowed())
            difference = sell_allowed_set.difference(set(currRanks))
            #print('difference', difference)
            #print("closing positions for orders not in curranks")
            if difference and sell_allowed_set:
                # ONE-LINE FIX - no async-generator crash
                for diff in difference:
                    #candlesDict[diff].in_slots = False
                    if await order_manager[diff].get_state() == "sell_allowed":
                        order_manager[diff].entry_by = 0
                        opentrade = 0

                await asyncio.gather(*[
                    order_manager[diff].submit_order(('sell', diff))
                    for diff in difference
                    if await order_manager[diff].get_state() == "sell_allowed"
                ])

                if TEST_MODE:
                    await asyncio.sleep(0.01)
                    await asyncio.gather(*[
                        order_manager[diff].execution_response({'order_status': 'partially_filled'})
                        for diff in difference
                        if await order_manager[diff].get_state() == "sell_pending"
                    ])
            #print("done closing positions")
            #print(len(currranks_set))
            #slot_timestamp = datetime.now(timezone.utc).timestamp()  
            for n, pair in enumerate(currRanks, start=1):
                if pair in candlesDict: 

                    state = await order_manager[pair].get_state() 

                    status = await system_status.get_status()
                    #print(ws_status.public, ws_status.private, ws_status.trades, 0 not in {ws_status.public, ws_status.private, ws_status.trades})
                    if opentrade != 1 and (state == "idle") and (status == 'online') and candlesDict[pair].intervals > 3800: #3600#interval_seconds  and (psrtpct < swppct < srtpct or (swppct < srtpct and pair != previous_slot_holding) or (sort_option[1] == "change_pct")): #spikepct > 0.001 | (slot_map[n - 1][1] != None) and | chgpct > swppct , pchgpct > swppct and pchgpct < chgpct, pspikepct > swppct and pspikepct < spikepct  #if slot_map[n - 1][0] == None and state == "idle" and chgpct > swppct:  and 0 not in {pspikepct, pchgpct, swppct} \                    
                        if 0 not in {ws_status.public, ws_status.private, ws_status.trades} and system_command == "Run":
                            #(last_wstatus, wstatus, wma_mom, last_dstatus, dstatus, 1 + (wma < middle) + (wma < lower))
                            #1 + (wma < middle) + (wma < lower)
                            async with candlesDict[pair].lock:                                 
                                rolling_wstatus = candlesDict[pair].rolling_wstatus
                                rolling_dstatus = candlesDict[pair].rolling_dstatus

                                wtradable = candlesDict[pair].wtradable
                                dtradable = candlesDict[pair].dtradable

                                candlesDict[pair].wtradable = False
                                candlesDict[pair].dtradable = False

                            cond1 = (wtradable) and (rolling_wstatus == (-1, 0, 1) or rolling_wstatus[1:] == (-1, 1))
                            cond2 = (dtradable) and (rolling_dstatus == (-1, 0, 1) or rolling_dstatus[1:] == (-1, 1)) and rolling_wstatus[-1] == 1

                            if cond1:
                                order_manager[pair].entry_by = 1
                            elif cond2:
                                order_manager[pair].entry_by = 2
                            else:
                                continue
                            opentrade = 1 #for demo
                            await order_manager[pair].submit_order(('buy', pair))

                            state = await order_manager[pair].get_state()
                            if (TEST_MODE) and state == "buy_pending":
                                await order_manager[pair].execution_response({'order_status':'partially_filled'})
                    elif state == "sell_allowed": #exit_on_swap_pct and ((state == "sell_allowed" and current_slot_holding == pair and chgpct < swppct) or (current_slot_holding != None and pair != current_slot_holding)):  
                      
                        async with candlesDict[pair].lock:
                            wstatus = candlesDict[pair].wstatus
                            dstatus = candlesDict[pair].dstatus

                        cond1 = wstatus == -1
                        cond2 = dstatus == -1
                    
                        if not (cond1 or cond2):
                            continue
                        #opentrade = 0 #for demo
                        entry_by = order_manager[pair].entry_by

                        if cond1 or (entry_by == 2 and cond2):
                            await order_manager[pair].submit_order(('sell', pair))
                            order_manager[pair].entry_by = 0

                        state = await order_manager[pair].get_state()  
                        if (TEST_MODE) and state == "sell_pending":
                            await order_manager[pair].execution_response({'order_status':'partially_filled'})   
            print(4)                
            await print_leaderboard()     
            prevRanks = currRanks  
            print('opentrade:',opentrade)
            await asyncio.sleep(0.000001) #0.000001

        except Exception as e:                        
            _, _, e_tb = sys.exc_info()               
            await system_log(f"{e_tb.tb_lineno} {e}", "EXCEPTION   ")
            await asyncio.sleep(1)
    #await system_log("Slot Trader", "STOPPED     ")
    #return

#q = asyncio.Queue(maxsize=50_000)

async def log(message, custom_timestamp = None, use_date = True):    
    # Convert UTC time to local time (EST/EDT)
    now = time.localtime()  # local time from system clock
    timestamp = time.strftime('%Y-%m-%d %H:%M:%S', now)

    filename = f"{time.strftime('%Y-%m-%d', now)}_{script_name}_trades.log".lower()
    filename = "/root/logs/" + filename if os.name == 'posix' else filename

    if not isinstance(message, str):
        message = str(message)

    is_new_file = not os.path.exists(filename)
    async with lock_manager.acquire('trd_log'):
        async with aiofiles.open(filename, mode='a', encoding='utf-8') as f:

            if is_new_file:
                await f.write(f"{log_header[0]}\n{log_header[1]}\n")

            if use_date:
                if custom_timestamp is not None:

                    await f.write(f'[{custom_timestamp}] {message}\n')
                else:
                    await f.write(f'[{timestamp}] {message}\n')
            else:
                await f.write(f'              {message}\n')
'''
async def system_log(message, category): ORIGINAL
    try:
        # Convert UTC time to local time (EST/EDT)
        now = time.localtime()  # local time from system clock
        timestamp = time.strftime('%Y-%m-%d %H:%M:%S', now)

        filename = f"{time.strftime('%Y-%m-%d', now)}_{script_name}_system.log".lower()
        filename = "/root/logs/" + filename if os.name == 'posix' else filename    

        if not isinstance(message, str):
            message = f"{message}"
   
        async with lock_manager.acquire('sys_log'):
            is_new_file = not os.path.exists(filename)
            async with aiofiles.open(filename, mode='a', encoding='utf-8') as f:

                if is_new_file:
                    await f.write(f"{system_log_header[0]}\n{system_log_header[1]}\n")

                await f.write(f'[{timestamp}] {category} {message}\n')
    except Exception:
        # last-resort visibility
        print("LOGGER FAILURE:", category, message, file=sys.stderr)
        traceback.print_exc()
'''
async def system_log(message, category):
    try:
        if not isinstance(message, str):
            message = str(message)

        now = time.localtime()
        timestamp = time.strftime('%Y-%m-%d %H:%M:%S', now)

        filename = f"{time.strftime('%Y-%m-%d', now)}_{script_name}_system.log".lower()
        if os.name == "posix":
            os.makedirs("/root/logs", exist_ok=True)
            filename = "/root/logs/" + filename

        async def _write():
            async with lock_manager.acquire("sys_log"):
                is_new_file = not os.path.exists(filename)
                async with aiofiles.open(filename, mode="a", encoding="utf-8") as f:
                    if is_new_file:
                        await f.write(f"{system_log_header[0]}\n{system_log_header[1]}\n")
                    await f.write(f"[{timestamp}] {category} {message}\n")
                    await f.flush()

        await asyncio.shield(_write())

    except Exception as e:
        _, _, e_tb = sys.exc_info() 
        await system_log(f"{e_tb.tb_lineno} {e} {message}", "LOGGER FAILURE")
"""
async def executions_log(message): ORIGINAL
    # Local time (EST/EDT based on system clock)
    now = time.localtime()
    #timestamp = time.strftime('%Y-%m-%d %H:%M:%S', now)

    filename = f"{time.strftime('%Y-%m-%d', now)}_{script_name}_executions.jsonl".lower()
    filename = "/root/logs/" + filename if os.name == 'posix' else filename

    log_entry = message
    '''
    {
        "timestamp": timestamp,
        "message": message,
    }
    '''
    # orjson.dumps returns bytes
    line = orjson.dumps(log_entry) + b"\n"

    async with lock_manager.acquire('executions_log'):
        async with aiofiles.open(filename, mode="ab") as f:
            await f.write(line)
"""

async def executions_log(message):
    try:
        # Local time (EST/EDT based on system clock)
        now = time.localtime()

        filename = f"{time.strftime('%Y-%m-%d', now)}_{script_name}_executions.jsonl".lower()
        filename = "/root/logs/" + filename if os.name == 'posix' else filename

        # orjson.dumps returns bytes
        line = orjson.dumps(message, default=str) + b"\n"

        async def _write():
            async with lock_manager.acquire("executions_log"):
                async with aiofiles.open(filename, mode="ab") as f:
                    await f.write(line)
                    await f.flush()  # helps a lot for restarts/cancels

        # Prevent websocket/task cancellation from interrupting the write
        await asyncio.shield(_write())

    except Exception as e:
        _, _, e_tb = sys.exc_info() 
        await system_log(f"{e_tb.tb_lineno} {e} {message}", "LOGGER FAILURE")

class Journal:
    FIXED_HEADERS = [
                        "DATE", "TIMESTAMP", "DAY", "ORDER ID", "TRADE ID",
                        "SYMBOL", "ORDER STATUS", "ORDER TYPE", "ACTION", "QUANTITY",
                        "ENTRY", "EXIT", "ENTRY BY", "EXIT BY", "PnL %", "SUBMISSION SUCCESS", "HIGHEST BID"
                    ]

    def __init__(self, base_dir: str = "trades"):
        #self.base_dir = "/root/" + Path(base_dir) if os.name == 'posix' else Path(base_dir)
        self.base_dir = Path(f"/root/{base_dir}") if os.name == "posix" else Path(base_dir)

        self._locks: dict[str, asyncio.Lock] = {}

    def _lock(self, fp: str) -> asyncio.Lock:
        if fp not in self._locks:
            self._locks[fp] = asyncio.Lock()
        return self._locks[fp]

    def _month_dir(self, dt: datetime) -> Path:
        return self.base_dir / dt.strftime("%b_%Y").upper()

    def _csv_path(self, dt: datetime) -> Path:
        return self._month_dir(dt) / f"{dt.strftime('%m_%d_%Y')}.csv"

    async def append(self, **data: Any) -> None:
        now = datetime.now(timezone.utc)
        csv_path = self._csv_path(now)

        async with self._lock(str(csv_path)):
            all_headers = self.FIXED_HEADERS  # ? ONLY your 15 headers

            # Build row
            row = [data.get(h.lower(), "") for h in all_headers]
            line = ",".join(f'"{x}"' if "," in str(x) or "\n" in str(x) else str(x) for x in row) + "\n"

            # Ensure dirs
            csv_path.parent.mkdir(parents=True, exist_ok=True)

            # Write
            async with aiofiles.open(csv_path, "a", newline="") as f:
                if csv_path.stat().st_size == 0:  # First write ? header
                    header_line = ",".join(f'"{h}"' for h in all_headers) + "\n"
                    await f.write(header_line)
                await f.write(line)

journal = Journal("trade_journals")

class log_Candles:
    '''
    __slots__ = (
            'istrending',
            'lock',
            'pair',
            'ask',
            'bid',
            'mid',
            'prices',
            'timestamp',
            'open',
            'high',
            'low',
            'pclose',
            'close',
            'volume',
            'base_volume',
            'starting_volume',
            'avol',
            'bvol',
            'pressure',
            'cum_pressure',
            'spread',
            'max_spread_pct',
            'spike_pct',
            'change_pct',
            'resettable_high',
            'range',
            'risk_score',
            'risk_pct',
            'max_risk_pct',
            'sec_running_cnt',
            'relative_risk',
            'current_timestamp',
            'starting_timestamp',
            'timeframe',
            'prev_spike_pct',
            'prev_change_pct',
            'stppct',
            'hitCount',
            'smma',
            'surge',
            'duration_data',
            'bid_high',
            'ask_high',
            'prev_price',
            'prev_ask',
            'prev_bid',
            'prev_mid',
            'prev_vol',
            'jump_pct',
            'prev_jump_pct',
            'stpprice',
            'tradable',
            'last_dir',
            'dir',
            'last_vol_dir',
            'vol_dir',
            'period',
            'offset',
            'highs',
            'lows',
            'closes',
            'bids',
            'asks',
            'current_minute',
            'current_bar',
            'prev_close',
            'window_bars',
            'bars',
            'donchian',
            'risk_cushion_pct',
            'd_spread_pct',
            'two_min_bar_max_spread',
            'current_max_spread',
            'max_spread',
            'position_risk',
            'atpr',
            'rsi',
            'adjusted_rsi',
            'prev_adjusted_rsi',
            'pct_frm_high',
            'stop_dist',
            'adjusted_change_pct',
            'adjusted_change_pct2',
            'interval_seconds',
            'intervals',
            'last_dstatus',
            'dstatus',
            'ticks',
            'data',
            'trending',
            'pct2_depth_usd',
            'sec_elapsed',
            'inflow',
            'spread_bps',
            'wmaH',
            'wmaL',
            'last_wmaH',
            'last_wmaL',
            'wma_mom',
            'wstatus',
            'w_spread_pct',
            'last_wstatus',
            'entry_by',
            'max_rolling_spread',
            'in_slots',
            'spreads',
            'spread_sum',
            'rolling_wstatus',
            'rolling_dstatus',
        )
        '''
    def __init__(self, info, restart=False):
        self.istrending = False
        self.lock = asyncio.Lock()
        info      = info['data'][0]
        self.pair = info['symbol']
        self.ask  = float(info["ask"])
        self.bid  = float(info["bid"])
        self.mid  = (self.ask + self.bid) / 2
        price     = (self.ask + self.bid) / 2 if last_type == 'mid' else float(info['last'])
        self.prices     = [self.mid]
        self.timestamp  = time.time()  #datetime.now(timezone.utc)   #time.time() #
        self.open       = self.bid
        self.high       = price
        self.low        = self.mid
        self.pclose     = -1
        self.close      = price
        self.volume     = float(info["volume"]) * self.ask #price
        self.base_volume     = float(info["volume"])
        self.starting_volume     = self.volume
        #self.cum_volume     = self.volume
        #self.volume_momentum = 'S'
        self.avol       = float(info["ask_qty"])
        self.bvol       = float(info["bid_qty"])
        self.pressure   = self.bvol - self.avol
        self.cum_pressure = self.pressure * price if self.bvol > self.avol else 0 
        #self.askprod         = [self.ask]
        self.spread      = 0 #pct
        self.max_spread_pct = 0
        self.spike_pct       = 0
        self.change_pct      = 0
        self.resettable_high = price
        self.range           = self.high - self.low
        self.risk_score      = 0
        self.risk_pct        = [self.risk_score]
        self.max_risk_pct    = self.risk_score
        #self.quota           = info["quota"]
        self.sec_running_cnt = 0
        self.relative_risk   = inf #smma(self.pair)        
        self.current_timestamp  = self.timestamp
        self.starting_timestamp = self.current_timestamp  

        self.timeframe       = timeframe if interval_seconds is None else "ROLLING"
        self.prev_spike_pct  = 0
        self.prev_change_pct = 0
        self.stppct          = 0

        self.hitCount = 0
        self.smma     = 0
        #H24_change_pct = float(info["change_pct"])
        #self.surge = (self.pressure / self.cum_pressure) * (1 + self.change_pct)
        #self.surge = (self.pressure / float(info["volume"])) * (1 + self.change_pct)
        
        #self.surge = (self.cum_pressure / self.volume) * (1 + self.spike_pct)
        self.duration_data = {
                "timestamps": [], "durations": [], "last_duration": 0.0,
                "cumulative_duration": 0.0, "duration_momentum": ""
            }
        self.bid_high   = self.bid
        self.ask_high   = self.ask
        self.prev_price = price
        self.prev_ask = self.ask
        self.prev_bid = self.bid
        self.prev_mid = self.mid
        self.prev_vol = self.volume
        self.jump_pct = 0
        self.prev_jump_pct = 0
        self.stpprice = 0
        self.wtradable = False
        self.dtradable = False
        self.last_dir = " "
        self.dir = " "
        self.last_vol_dir = " "
        self.vol_dir = " "
        
        self.period = 6
        self.offset = 1
        self.highs, self.lows, self.closes, self.bids, self.asks = [], [], [], [], []
        self.current_minute = int(time.time() // 60 * 60)
        self.current_bar = {}#{'open': None, 'high': None, 'low': None, 'close': 0, 'prev_close': None}
        self.prev_close = None
        self.window_bars = {}

        #self.minute_ohlc(self.bid, self.ask)
        #self.spreadfil = self.spread_to_atr_max_ema(bids, asks, highs, lows, closes)
        #self.spreadfil = self.is_avg_spread_gt_atr(bids, asks, highs, lows, closes)
        self.risk_cushion_pct = 0
        self.d_spread_pct = 0
        self.w_spread_pct = 0
        self.two_min_bar_max_spread = 0
        self.current_max_spread = -inf
        self.max_spread = self.current_max_spread
        self.position_risk = 0
        self.atpr = 0
        self.rsi = 0
        self.adjusted_rsi = 0
        self.prev_adjusted_rsi = 0
        self.pct_frm_high = 0
        self.stop_dist = 0
        self.interval_seconds = interval_seconds
        self.intervals = 0
        self.last_dstatus = 0
        self.dstatus = 0        
        if not restart and interval_seconds is not None:
            self.ticks = deque()                  # will store (datetime, price, volume)
        elif interval_seconds == None:
            self.ticks = None
        self.donchian = {'upper': inf, 'lower': -inf, 'middle': 0, 'direction': 'u'}
        self.donchian_dir = 0
        self.data = info
        self.trending = False
        self.pct2_depth_usd = 0
        self.sec_elapsed = 0
        self.inflow = 0
        self.spread_bps = 0
        self.max_rolling_spread = inf
        self.wmaH = 0
        self.wmaL = 0
        self.last_wmaH = 0
        self.last_wmaL = 0
        self.wma_mom = 0
        self.wstatus = 0
        self.last_wstatus = 0
        self.in_slots = False
        self.spreads = deque()
        self.spread_sum = 0.0       
        self.rolling_wstatus = (0,0,0)  
        self.rolling_dstatus = (0,0,0)
        self.last_rolling_wstatus = (0,0,0)
        self.last_rolling_dstatus = (0,0,0)
        self.wstatus_shifted = 0
        self.dstatus_shifted = 0

    async def update2(self, info):
        try:
            async with self.lock:

                infoupdate = info['data'][0]
                bid = float(infoupdate["bid"])
                ask = float(infoupdate["ask"])
                mid  = (ask + bid) / 2

                self.prev_mid   = self.mid
                self.prev_bid   = self.bid
                self.prev_ask   = self.ask

                self.ask = ask
                self.bid = bid
                self.mid = mid
                #self.spread      = (self.ask - self.bid) / self.bid  #percent

                #self.timestamp = datetime.now(timezone.utc).timestamp()
                self.timestamp = time.time()

                self.ticks.append((self.timestamp, self.mid, self.bid, self.ask)) #0 for volume

                
                spread = (self.ask - self.bid) / self.bid

                self.spreads.append(spread)
                #self.spread_sum += spread

                cutoff_now = self.timestamp - interval_seconds
                #cutoff_now = time.time() - interval_seconds 
                while self.ticks and self.ticks[0][0] < cutoff_now:                      
                    self.ticks.popleft()
                    old_spread = self.spreads.popleft()
                    #self.spread_sum -= old_spread

                if self.ticks:                      
                    self.intervals = self.timestamp - self.ticks[0][0]

                    if self.spreads:
                        #self.spread_bps = self.spread_sum / len(self.spreads)
                        self.max_rolling_spread = max(self.spreads)   # can optimize further if needed
                    else:
                        self.max_rolling_spread = inf
                    whigh = max([t[3] for t in self.ticks])  
                    wlow  = min([t[1] for t in self.ticks])

                    wopen  = self.ticks[0][1]                  # first tick in window
                    wclose = self.ticks[-1][1]                # last tick in window

                    #self.spike_pct = ((wclose - wlow) / wlow) if wlow != wclose else 0
                    #self.spike_pct = (wclose - wlow) / wlow if wlow != 0 else 0

                    self.change_pct = {
                                        'ret'                 : ((wclose - wopen) / wopen) - self.max_rolling_spread, 
                                        'inflows'             : ( wclose - wopen) / wopen,
                                        'inflow_weighted_ret' : self.inflow * (((wclose - wopen) / wopen) - self.max_rolling_spread)
                                      }[sort_option]

                    #if self.in_slots:
                    upper, lower = self.donchian['upper'], self.donchian['lower']
                    if self.pair in currranks_set or (whigh < upper and wlow > lower):
                        snapshot60 = await self.ticks_snapshot()
                        if (snapshot60 == None) or len(snapshot60) < 3:
                            return
                        
                        donchian_history = await self._calculate_donchian(snapshot60, 360, 60, 3800)

                        if len(donchian_history) >= 4:

                            await self.donchian_status(snapshot60, donchian_history)

                            self.wmaL, second_last_wmal, third_last_wmal = await self.weighted_moving_average(donchian_history, 3600, 60)
                            self.wmaH, second_last_wmah, third_last_wmah = await self.weighted_moving_average(donchian_history, 3600, 60, 'upper')

                            self.wstatus  = 1 if self.mid > self.wmaH else -1 if self.mid < self.wmaL else 0
                            self.wstatus2 = 1 if snapshot60[-2][1] > second_last_wmah else -1 if snapshot60[-2][1] < second_last_wmal else 0
                            self.wstatus3 = 1 if snapshot60[-3][1] > third_last_wmah else -1 if snapshot60[-3][1] < third_last_wmal else 0

                            # ------
                            self.last_rolling_wstatus = self.rolling_wstatus 
                            self.rolling_wstatus = (self.wstatus3, self.wstatus2, self.wstatus) 
                            shifted = self.rolling_wstatus[2] != self.last_rolling_wstatus[2] 

                            self.wtradable = True if shifted else False
                            # ------

            self.data = info
        except Exception as e:
            _, _, e_tb = sys.exc_info()                                                                 
            await system_log(f"{e_tb.tb_lineno} Exception in candles dict update for {self.pair}: {e}", "EXCEPTION  ")
            await asyncio.sleep(1)
    async def update(self, info):
        try:
            # ---------- FAST SECTION: mutate shared state + snapshot ----------
            async with self.lock:
                infoupdate = info["data"][0]
                bid = float(infoupdate["bid"])
                ask = float(infoupdate["ask"])
                mid = (ask + bid) / 2

                self.prev_mid = self.mid
                self.prev_bid = self.bid
                self.prev_ask = self.ask

                self.ask = ask
                self.bid = bid
                self.mid = mid

                self.timestamp = time.time()

                # append tick + spread
                self.ticks.append((self.timestamp, self.mid, self.bid, self.ask))
                spread = (self.ask - self.bid) / self.bid
                self.spreads.append(spread)

                # prune window
                cutoff_now = self.timestamp - interval_seconds
                while self.ticks and self.ticks[0][0] < cutoff_now:
                    self.ticks.popleft()
                    self.spreads.popleft()

                # snapshot for calculations (cheap & prevents long lock holds)
                ticks = tuple(self.ticks)      # each tick: (ts, mid, bid, ask)
                spreads = tuple(self.spreads)

                # capture gating variables you use later
                mid_now = self.mid
                inflow = self.inflow
                donch_upper = self.donchian["upper"]
                donch_lower = self.donchian["lower"]
                in_ranked = self.pair in currranks_set

                # store raw info at end (no need to lock if only this task writes it,
                # but keep here since you're already in lock)
                self.data = info

            # ---------- SLOW SECTION: compute derived metrics OUTSIDE lock ----------
            if not ticks:
                return

            intervals = ticks[-1][0] - ticks[0][0]
            max_rolling_spread = max(spreads) if spreads else float("inf")

            # Your window stats
            whigh = max(t[3] for t in ticks)   # max ask
            wlow  = min(t[1] for t in ticks)   # min mid
            wopen  = ticks[0][3]
            wclose = ticks[-1][2]
            #((self.timestamp, self.mid, self.bid, self.ask)) 0 1 2 3
            # returns
            inflows_ret = (wclose - wopen) / wopen if wopen else 0.0
            ret = inflows_ret - max_rolling_spread
            change_pct = {
                "ret": ret,
                "inflows": inflows_ret,
                "inflow_weighted_ret": inflow * ret,
            }[sort_option]

            # Optional: write derived fields back under lock (recommended if other tasks read them)
            async with self.lock:
                self.intervals = intervals
                self.max_rolling_spread = max_rolling_spread
                self.change_pct = change_pct

            # ---------- More heavy work (and awaits) OUTSIDE lock ----------
            # gate condition (same as your code)
            if in_ranked or (whigh < donch_upper and wlow > donch_lower):
                # Ideally ticks_snapshot() should NOT take the same lock for long.
                # If it does, refactor it to just snapshot quickly like above.
                snapshot60 = await self.ticks_snapshot()
                if (snapshot60 is None) or len(snapshot60) < 3:
                    return

                donchian_history = await self._calculate_donchian(snapshot60, 360, 60, 3800)
                if len(donchian_history) < 4:
                    return

                await self.donchian_status(snapshot60, donchian_history)

                wmaL, second_last_wmal, third_last_wmal = await self.weighted_moving_average(
                    donchian_history, 3600, 60
                )
                wmaH, second_last_wmah, third_last_wmah = await self.weighted_moving_average(
                    donchian_history, 3600, 60, "upper"
                )

                wstatus  = 1 if mid_now > wmaH else -1 if mid_now < wmaL else 0
                wstatus2 = 1 if snapshot60[-2][1] > second_last_wmah else -1 if snapshot60[-2][1] < second_last_wmal else 0
                wstatus3 = 1 if snapshot60[-3][1] > third_last_wmah else -1 if snapshot60[-3][1] < third_last_wmal else 0

                async with self.lock:
                    self.wmaL = wmaL
                    self.wmaH = wmaH

                    self.wstatus = wstatus
                    self.wstatus2 = wstatus2
                    self.wstatus3 = wstatus3

                    last = self.rolling_wstatus
                    self.last_rolling_wstatus = last
                    self.rolling_wstatus = (wstatus3, wstatus2, wstatus)

                    shifted = self.rolling_wstatus[2] != last[2]
                    self.wtradable = True if shifted else False

        except Exception as e:
            _, _, e_tb = sys.exc_info()
            await system_log(
                f"{e_tb.tb_lineno} Exception in candles dict update for {self.pair}: {e}",
                "EXCEPTION  ",
            )
            await asyncio.sleep(1)
    def stop_pct(self, condition):
        if condition == 1:
            return (self.max_rolling_spread + ((self.wmaH - self.wmaL) / self.wmaH)) * 2
        if condition == 2:
            return (self.max_rolling_spread + self.d_spread_pct) * 2

    async def _calculate_donchian(self, ticks, period: float, offset: float, historical_window: float):        
        try:
            if not ticks:
                #await self.donchian_status()
                return []

            # If ticks is a deque of (ts, mid, bid, ask) from ticks_snapshot
            # Convert once (O(n)) so indexing is fast
            if isinstance(ticks, deque):
                data = list(ticks)
            else:
                data = ticks

            n = len(data)
            if n < 2:
                #await self.donchian_status()
                return []

            # Derive sampling step (seconds) from data
            # fallback to 60 if weird
            dt = data[1][0] - data[0][0]
            if dt <= 0:
                dt = 60.0

            period_pts = int(period // dt)
            offset_pts = int(offset // dt)

            if period_pts <= 0:
                #await self.donchian_status()
                return []

            # We'll compute rolling max ask and rolling min bid over 'period_pts'
            # Using monotonic queues: O(n)
            asks = [x[3] for x in data]
            bids = [x[2] for x in data]
            tss  = [x[0] for x in data]

            _dq = deque
            maxq = _dq()  # indices, asks decreasing
            minq = _dq()  # indices, bids increasing

            roll_max_ask = [None] * n
            roll_min_bid = [None] * n

            for i in range(n):
                a = asks[i]
                b = bids[i]

                # maintain maxq for asks
                while maxq and asks[maxq[-1]] <= a:
                    maxq.pop()
                maxq.append(i)
                # expire old
                while maxq and maxq[0] <= i - period_pts:
                    maxq.popleft()

                # maintain minq for bids
                while minq and bids[minq[-1]] >= b:
                    minq.pop()
                minq.append(i)
                while minq and minq[0] <= i - period_pts:
                    minq.popleft()

                # Only valid once window is full
                if i >= period_pts - 1:
                    roll_max_ask[i] = asks[maxq[0]]
                    roll_min_bid[i] = bids[minq[0]]

            latest_ts = tss[-1]
            min_ts = latest_ts - historical_window

            # We want windows ending at t_end = ref_ts - offset.
            # With discrete samples: end_index = i - offset_pts
            # Start making history from the most recent valid end index.
            end_i = n - 1 - offset_pts
            if end_i < period_pts - 1:
                #await self.donchian_status()
                return []

            step_pts = max(1, int(period // dt))  # Donchian cadence
            history = []

            # Walk backwards in steps of 'period' (in points)
            i = end_i
            while i >= period_pts - 1 and tss[i] >= min_ts:
                hi = roll_max_ask[i]
                lo = roll_min_bid[i]
                if hi is not None and lo is not None:
                    d_mid = (hi + lo) * 0.5
                    history.append((tss[i], hi, d_mid, lo))
                i -= step_pts

            if not history:
                return []

            history.reverse()

            # Current Donchian from most recent
            _, current_upper, current_mid, current_lower = history[-1]
            self.donchian = {"upper": current_upper, "lower": current_lower, "middle": current_mid}

            if current_lower != 0:
                self.d_spread_pct = (current_upper - current_lower) / current_lower
            else:
                self.d_spread_pct = 0.0

            #await self.donchian_status()
            return history

        except Exception as e:                                    
            await system_log(f"{e.__traceback__.tb_lineno} {e}", "EXCEPTION   ")
            await asyncio.sleep(1)
            return []


    '''
    async def _calculate_donchian(self, ticks, period: float, offset: float, historical_window: float):
        try:
            #ticks = self.ticks
            if not ticks:
                await self.donchian_status()
                return []

            #buckets = minute_aligned_buckets(ticks[-1][0], interval, offset, historical_window)
            latest_ts = ticks[-1][0]
            # how many historical samples we can compute
            history = []

            # step size = period (natural Donchian cadence)
            step = period

            ref_ts = latest_ts

            while ref_ts >= latest_ts - historical_window:
                t_end = ref_ts - offset
                t_start = t_end - period

                hi = -1e308
                lo =  1e308
                found = False

                # iterate newest → oldest (deque is time ordered)
                for i in range(len(ticks) - 1, -1, -1):
                    ts, _, bid, ask, *_ = ticks[i]

                    if ts > t_end:
                        continue
                    if ts < t_start:
                        break

                    found = True
                    if ask > hi:
                        hi = ask
                    if bid < lo:
                        lo = bid

                if not found:
                    ref_ts -= step
                    continue

                d_mid = (hi + lo) * 0.5
                #prev_mid = self.donchian['middle']
                #ddir = 'u' if d_mid > prev_mid else 'd' if d_mid < prev_mid else 's'

                history.append((ts, hi, d_mid, lo))

                ref_ts -= step

            if not history:
                return []

            # last entry is most recent (as requested)
            history.reverse()

            # current Donchian = last element
            _, current_upper, current_mid, current_lower = history[-1]

            self.donchian = {'upper': current_upper, 'lower': current_lower, 'middle': current_mid}

            if current_lower != 0:
                self.d_spread_pct = (current_upper - current_lower) / current_lower
            else:
                self.d_spread_pct = 0.0 

            await self.donchian_status()

            return history
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION  ")
            await asyncio.sleep(1)
    '''
    async def donchian_status(self, tick_hist, donchian_hist):
        if len(donchian_hist) < 3:
            self.rolling_dstatus = (0, 0, 0)
            return
        #dprice1, dprice2 = method[1].values()
        try:
            _, _, bid, ask = tick_hist[-1] #snap, last_mid, last_bid, last_ask
            _, _, bid2, ask2 = tick_hist[-2] #snap, last_mid, last_bid, last_ask
            _, _, bid3, ask3 = tick_hist[-3] #snap, last_mid, last_bid, last_ask
            prev_close = self.prev_mid
            #upper, middle, lower = self.donchian['upper'], self.donchian['middle'], self.donchian['lower']
            _, upper, middle, lower = donchian_hist[-1] #tss[i], hi, d_mid, lo
            _, upper2, middle2, lower2 = donchian_hist[-2]
            _, upper3, middle3, lower3 = donchian_hist[-3]
            if None in (upper, lower, prev_close, self.prev_ask, self.prev_bid):
                return

            self.dstatus  = 1 if bid  > middle  else -1 if  ask < lower  else 0
            self.dstatus2 = 1 if bid2 > middle2 else -1 if ask2 < lower2 else 0
            self.dstatus3 = 1 if bid3 > middle3 else -1 if ask3 < lower3 else 0

            # ---  
            self.last_rolling_dstatus = self.rolling_dstatus 
            self.rolling_dstatus = (self.dstatus3, self.dstatus2, self.dstatus) 
            shifted = self.rolling_dstatus[2] != self.last_rolling_dstatus[2] 

            self.dtradable = True if shifted else False
            # ---
            self.donchian_dir = 1 if middle > middle2 else -1 if middle < middle2 else 0
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e} {tick_hist[-1]}","EXECUTION  ")
            await asyncio.sleep(1)

    async def weighted_moving_average(self, prices: list, window: float, segmentation: float = 0.0, price_type = 'lower') -> Optional[float]:
        ptype = {'upper':1, 'lower':3}[price_type]
        try:
            if not prices:
                return 0,0,0
            second_last = 0
            third_last = 0
            t_latest = prices[-1][0]
            t_start = t_latest - window

            weighted_sum = 0.0
            weight_total = 0.0

            weight = 1.0  # newest tick gets highest weight
            last_sample_ts = None

            # newest → oldest
            for i in range(len(prices) - 1, -1, -1):
                ts = prices[i][0]

                if ts < t_start:
                    #break
                    continue
                # enforce segmentation
                if last_sample_ts is not None and (last_sample_ts - ts) < segmentation:
                    continue

                price = prices[i][ptype] #0 timestamp 1 upper 3 middle 3 lower

                weighted_sum += price * weight
                weight_total += weight

                weight += 1.0
                last_sample_ts = ts

                if prices[-2][0] == ts:
                    second_last = weighted_sum / weight_total

                if prices[-3][0] == ts:
                    third_last = weighted_sum / weight_total

            if weight_total == 0.0:
                return 0,0,0

            return weighted_sum / weight_total, second_last, third_last
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION  ")
            await asyncio.sleep(1)

    async def ticks_snapshot(self, interval=60, window_sec=3800):
        dq = self.ticks
        if not dq:
            return None

        end_ts = dq[-1][0]
        window_start = end_ts - window_sec

        # Start snap aligned to interval, and >= window_start
        ts0 = dq[0][0]
        snap = ts0 - (ts0 % interval) + interval
        if snap < window_start:
            snap = window_start - (window_start % interval) + interval

        out = deque()
        append = out.append

        # carry-forward last known values
        _, last_mid, last_bid, last_ask = dq[0]

        for i in range(1, len(dq)):
            ts, mid, bid, ask = dq[i]

            if ts >= snap:
                # how many snapshots fall between [snap, ts]
                k = int((ts - snap) // interval) + 1
                for _ in range(k):
                    append((snap, last_mid, last_bid, last_ask))
                    snap += interval

            last_mid, last_bid, last_ask = mid, bid, ask

            # Optional: if snap already beyond end_ts, we can stop early
            if snap > end_ts:
                break

        # If we produced nothing, fall back to raw dq (your original behavior)
        return out if out else dq

    '''
    async def ticks_snapshot(self, interval=60, window_sec=3800):
        out = deque()
        dq = self.ticks
        if not dq:
            return dq

        # last timestamp defines the window end
        end_ts = dq[-1][0]
        window_start = end_ts - window_sec

        ts0, last_mid, last_bid, last_ask, _, _ = dq[0]  #(self.timestamp, self.mid, self.bid, self.ask, 0, 0)

        # snapshot clock starts at max(first interval, window start)
        snap = ts0 - (ts0 % interval) + interval
        if snap < window_start:
            snap = window_start - (window_start % interval) + interval

        append = out.append
        step = interval

        for i in range(1, len(dq)):
            ts = dq[i][0]

            while snap <= ts:
                append((snap, last_mid, last_bid, last_ask))
                snap += step
            
            #last_mid = dq[i][1]
            _, last_mid, last_bid, last_ask, _, _ = dq[i]
            #await asyncio.sleep(0)
        if not out:
            return dq
        return out
    '''
    async def insert(self, key, value):
        async with self.lock:
            setattr(self, key, value)

    async def get(self, key):
        async with self.lock:
            return getattr(self, key)

    async def get_many(self, keys):
        async with self.lock:
            return [getattr(self, key, "") for key in keys]

    async def set(self, key, value):
        async with self.lock:
            setattr(self, key, value)

# Kraken WebSocket API URL
#KRAKEN_WS_URL      = "wss://ws.kraken.com/"
#KRAKEN_WS_AUTH_URL = "wss://ws-auth.kraken.com/v2" #wss://ws-auth.kraken.com/v2

#KRAKEN_WS_URL      = "wss://beta-ws.kraken.com/v2"	
#KRAKEN_WS_AUTH_URL = "wss://beta-ws-auth.kraken.com/v2"

WAITING_STATUS = False 

api_key = 'qka9r7Do8CMbPcWtbcBfl8DPqi7lVZySx32AJz14yMwXU9ajGhG8TQ29'
secret  = 'v/tAeQuS8DZgBIm/7e+NH+o2vqu9yh4tzoA+bMwVc4qq6s/KvnJN6uI/HjLptjmJxCbLi/w26htgvEubARuUCg=='

def get_kraken_signature(urlpath, data):
    
    postdata = urllib.parse.urlencode(data)
    encoded = (str(data['nonce']) + postdata).encode()
    message = urlpath.encode() + hashlib.sha256(encoded).digest()

    mac = hmac.new(base64.b64decode(secret), message, hashlib.sha512)
    sigdigest = base64.b64encode(mac.digest())
    return sigdigest.decode()

def kraken_request(uri_path, data = {}):
    data["nonce"] = str(int(1000*time.time()))
    api_url = "https://api.kraken.com"

    headers = {}
    headers['API-Key'] = api_key
    # get_kraken_signature() as defined in the 'Authentication' section
    headers['API-Sign'] = get_kraken_signature(uri_path, data)             
    req = requests.post((api_url + uri_path), headers=headers, data=data)
    return req

def sec_sleep(response_date):
    while (datetime.now(timezone.utc) - response_date).total_seconds() <= 1:
        continue

def generate_kraken_signature(endpoint, nonce, api_secret):
    """Generate Kraken API authentication signature."""
    message = endpoint + hashlib.sha256(nonce.encode()).hexdigest()
    signature = hmac.new(
        base64.b64decode(api_secret),
        message.encode(),
        hashlib.sha512
    ).digest()
    return base64.b64encode(signature).decode()

async def send_message(ws, message):
    """Send a message to the WebSocket."""
    await ws.send(orjson.dumps(message))
    #print(f"Sent: {message}")

async def subscribe(ws, message):
    #await rate_limiter.limit()
    """Subscribe to a channel (public or private)."""
    await send_message(ws, message)

async def unsubscribe(ws, message):
    #await rate_limiter.limit()
    """Unsubscribe from a channel."""
    await send_message(ws, message)
#@exception_decorator()
async def Process_Public_Message(message):

    global ohlc_subscriptions, prev_df, ticker_prices, instrument_dict, balance_checked, subList, order_manager, candlesDict, pending_events#ujson

    if ("method" in message): 
        if message["method"] == "subscribe" and message['result']['channel'] != 'ticker':            
            await system_log(message, "SUBSCRIPTION")

    try:
        if "channel" in message:
            if message['channel'] == 'status': #message["channel"] == "status" and message["type"] == "update"
                status = message['data'][0]['system']
                await system_status.set_status(status)
                await system_log(status, "SYS STATUS  ")                                        
            if message["channel"] == "ohlc":
                #await update_dataframe(ws, message, message["type"])
                #await update_dataframe(message, message["type"])
                pass
            if message["channel"] == 'ticker':   
                #print(message)       
                #timestamp = await get_current_timestamp()
                for entry in message['data']:

                    pair = entry['symbol']  
                    #if pair not in bars_dict:
                    #    bars_dict[pair] = {} 
                    #    l = #THIS IS CAUSING THE ISSUES / CREATE FUNCTIONS FOR INIT CANDLESDICT AND ORDERMANAGER
                    #async with lock_manager.acquire(f'{pair}_objects_create'):    

                    if pair in candlesDict:  #candlesDict
                        await candlesDict[pair].update(message) 
                         
                        if sort_option == "ret":
                            ret, inflow = await candlesDict[pair].get_many(['change_pct', 'inflow'])
                            if ret > 0: 
                                await sl.update(pair, ret) 
                            elif (ret < 0) or pair in sl._list[:-15] or '0' == str(candlesDict[pair].intervals).split('.')[0]: # or wma == 0
                                await sl.remove(pair)
                        elif sort_option == "inflows":
                            ret, inflow = await candlesDict[pair].get_many(['change_pct', 'inflow'])
                            if ret > 0 and inflow > 0: 
                                await sl.update(pair, inflow)
                            elif inflow == 0 or pair in sl._list[:-15] or '0' == str(candlesDict[pair].intervals).split('.')[0]: # or wma == 0
                                await sl.remove(pair)
                            else:
                                await sl.remove(pair)
                        elif sort_option == "inflow_weighted_ret":
                            ret, inflow, ticks = await candlesDict[pair].get_many(['change_pct', 'inflow', 'ticks'])
                            first = ticks[0][3]                 
                            last  = ticks[-1][2] 
                            #((self.timestamp, self.mid, self.bid, self.ask))
                            if last > first and ret > 0 and inflow > 0: 
                                await sl.update(pair, ret)
                            elif inflow == 0 or pair in sl._list[:-15] or '0' == str(candlesDict[pair].intervals).split('.')[0]: # or wma == 0
                                await sl.remove(pair)
                            else:
                                await sl.remove(pair)
                        #if pair in currranks_set | set(osd.order_state_dict['buy_pending'] + osd.order_state_dict['sell_allowed'] + osd.order_state_dict['sell_pending']):
                            #pending_events.append(1)
                            #await pending_events.put(1)
                        
                    #await sort_spikes(entry['symbol'])
                    #asyncio.create_task(sort_spikes(entry['symbol']))
                    #print(sorted_spikes[-10:][-1], candlesDict[pair].spike_pct)

            if (message["channel"] == "instrument") and message["type"] in ["snapshot", "update"]:               
                #instrument_dict = {pair['symbol'] : pair for pair in message['data']['pairs'] if (pair['status'] == 'online') and ("USD" == pair['symbol'].split('/')[1]) and not any(currency in pair['symbol'] for currency in stablecoins)}
                for pairinfo in message['data']['pairs']:
                    if (pairinfo['status'] == 'online') and ("USD" not in pairinfo['symbol'].split('/')[0]) and ("USD" == pairinfo['symbol'].split('/')[1]) and not any(currency in pairinfo['symbol'] for currency in stablecoins):                       
                        if pairinfo['symbol'] not in instrument_dict:
                            instrument_dict[pairinfo['symbol']] = pairinfo 
                            
                        if pairinfo['symbol'] not in candlesDict:
                            init_candle = {"channel": "ticker","type":"update","data":[{"symbol": pairinfo['symbol'],"bid": 0,"bid_qty": 0,"ask": 0,"ask_qty": 0,"last": 0,"volume": 0,"vwap": 0,"low": 0,"high": 0,"change": 0,"change_pct": 0}]}
                            candlesDict[pairinfo['symbol']] = log_Candles(init_candle)
                        if pairinfo['symbol'] not in order_manager:
                            order_manager[pairinfo['symbol']] = OrderManager(pairinfo['symbol'])
                        
                    elif pairinfo['status'] != 'online' and pairinfo['symbol'] in instrument_dict:
                        instrument_dict.pop(pairinfo['symbol'], None)
                        candlesDict.pop(pairinfo['symbol'], None)   
                        order_manager.pop(pairinfo['symbol'], None)
                        subList.discard(pairinfo['symbol'])
                        public_ws.subscription_queues.pop(pairinfo['symbol'], None)
                        public_ws._inflight.discard(pairinfo['symbol'])                        
                    else:
                        continue
                        #await public_ws.set('InstrumentDict', {pairinfo['symbol'] : pairinfo}, 'update') ---

                #subList = list(instrument_dict.keys()) 
                #unique_new_pairs = list(set(instrument_dict.keys()) - set(subList))
                #print(unique_new_pairs)
                #print(message["channel"] , message["type"],subList)
                chunks = 200
                #---------------------------------------------------------------------------
                if public_ws.is_restart:
                    public_ws.is_restart = False
                    subList = set()
                    '''
                    for i in range(0, len(subList), chunks):
                        resSub = subList[i:i + chunks]                        
                        #subPairs = await sl.get_symbols(chunks)
                        #resSub = await sl.get_symbols(50) 
                        tickData = {    
                                        "method" : "subscribe",
                                        "params" : {
                                                        "channel"       : "ticker",
                                                        "symbol"        : resSub,
                                                        "event_trigger" : "bbo",
                                                        "snapshot"      : False
                                                   }
                                   } 
                        await subscribe(public_ws.ws, tickData)

                        #subList |= set(subPairs)
                    '''
                #----------------------------------------------------------------------------
                unique_new_pairs = set(instrument_dict) - subList
                unique_new_pairs = list(unique_new_pairs)

                for i in range(0, len(unique_new_pairs), chunks):
                    subPairs = unique_new_pairs[i:i + chunks]  # Get two elements (or one if at the end)
                    tickData = {    
                                    "method" : "subscribe",
                                    "params" : {
                                                    "channel"       : "ticker",
                                                    "symbol"        : subPairs,
                                                    "event_trigger" : "bbo",
                                                    "snapshot"      : False
                                               }
                               }                   
                    await system_log(f"Tickers: {', '.join(subPairs)}", "SUBSCRIPTION")
                    await public_ws.send(tickData)

                balance_checked = True

                subList |= set(instrument_dict)

        if "error" in message:
            await system_log(f"{message}", "WS PUB ERROR")

    except Exception as e:                                 
        await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION   ")
        await asyncio.sleep(1)

#seen_exec_ids = deque(maxlen=10)
#@exception_decorator()
async def Process_Private_Message(message):
        global df, balances_df, ticker_prices, usd_balance, balance_dict, liquid_pairs, session_balance, seen_exec_ids, order_manager       
        """Called when a message is received."""

        if ("channel" in message) and 'heartbeat' == message['channel']:
            pass
        try:
            if ("method" in message) and 'add_order' == message['method']:
                rid, aid = str(message.get("req_id"))
                pair = await allocator.get_id_for_asset(int(aid))
                await system_log(f"{pair} {message}", "ADD ORDER   ")
                ordermanager = order_manager[pair]   
                if message['success']: 
                    #oid = message.get("order_id")
                    order_manager[pair].order_ack(message)                   
                else:               
                    async with ordermanager.lock:

                        await osd.order_state_dict_remove(ordermanager.state, pair)
                        await allocator.release_allotment(aid) 
                     
                        order_manager[pair].state        = "idle"
                        order_manager[pair].pos_qty      = 0
                        order_manager[pair].entry_by     = 0
                        order_manager[pair].allotment_id = -1

            if "channel" in message:
                if message["channel"] == "balances":
                    if message["type"] in ["snapshot", "update"]:
                        for balance in message["data"]:
                            if balance["asset"] == "USD":
                                usd_balance = balance["balance"] 
                                if balances.session == 0:
                                    await balances.update('session', usd_balance)
                                await balances.update('USD', usd_balance)
                                #async with lock_manager.acquire('balances'):
                                #balance_dict.update({balance["asset"] : balance["balance"]})
                            else:
                                await balances.update(balance["asset"], balance["balance"])

                            await system_log(balance, f'{balance["asset"]} BALANCE {message["type"]}')
                if (message["channel"] in {"executions", "open_orders", "own_trades", "openorders", "owntrades"}):                                                
                    await system_log(f"{message}", "EXECUTION   ")
                   
                    await limiter.feed(message)                             
                    for entry in message["data"]:
                        if message["data"]:
                            #exec_id = entry.get('exec_id')
                            #timestamp = entry.get('timestamp')

                            pair = entry.get("symbol", None)

                            if (pair != None) and pair not in order_manager:
                                order_manager[pair] = OrderManager(pair)

                            #order_state_set = set(await osd.get_all_order_state_list())
                            sell_allowed = set(await osd.get_sell_allowed())
                            buy_pending  = set(await osd.get_buy_pending())

                            if pair in sell_allowed | buy_pending: #if pair in order_state_set:
                       
                                if (pair != None) and (entry["exec_type"] == "trade"):                      
                                    #await order_manager[pair].execution_response(message)
                                    if  (order_manager[pair].ack_check(entry, False)) and ((entry["side"] == "buy" and pair in buy_pending) or (entry["side"] == "sell" and pair in sell_allowed)):
                                        #save execution log
                                        await order_manager[pair].execution_response(entry)
                                        await executions_log(entry)
                                else:
                                    await system_log(f"1 {entry}", "NOT TRADE ENTRY DATA")
                                    entry.update({'1':"NOT TRADE ENTRY DATA"})
                                    await executions_log(entry)
                                    #MAYBE UPDATE EXISTING EXECUTION ENTRY HERE
                                    #order_manager[pair].execution.update(entry)
                                #global pending_events, currranks_set
                                #if pair in currranks_set | set(osd.order_state_dict['buy_pending'] + osd.order_state_dict['sell_allowed'] + osd.order_state_dict['sell_pending']):
                                #    await pending_events.put(1)
                            else:
                                await system_log(f"2 {entry}", "NOT TRADE ENTRY DATA")
                                entry.update({'2':"NOT IN OSD"})
                                await executions_log(entry)
                                #await executions_log(entry)

            if "error" in message:
                await system_log(f"{message}", "WS PRI ERROR")

            if 'heartbeat' in message:
                #await ohlc_sub_manager()
                pass
        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXECUTION  ")
            await asyncio.sleep(1)

# ----------------------------------------------------------------------
#  Central status holder (replaces the old globals; optional if slot_trader doesn't need it)
# ----------------------------------------------------------------------
class WSStatus:
    def __init__(self):
        self.lock    = asyncio.Lock()
        # -1 = not started, 0 = down, 1 = up
        self.public  = -1      
        self.private = -1
        self.book    = -1
        self.trades  = -1

    async def set_public(self, v: int):
        async with self.lock:
            self.public = v

    async def set_private(self, v: int):
        async with self.lock:
            self.private = v

    async def set_book(self, v: int):
        async with self.lock:
            self.book = v

    async def set_trades(self, v: int):
        async with self.lock:
            self.trades = v

    async def is_public_up(self) -> bool:
        async with self.lock:
            return self.public == 1

    async def is_private_up(self) -> bool:
        async with self.lock:
            return self.private == 1

    async def is_book_up(self) -> bool:
        async with self.lock:
            return self.book == 1

    async def is_trades_up(self) -> bool:
        async with self.lock:
            return self.trades == 1

ws_status = WSStatus()

class FixedTimer:
    __slots__ = ("interval", "target", "lock")

    def __init__(self, interval_seconds: int):
        self.interval = interval_seconds
        self.target = None
        self.lock = asyncio.Lock()

    async def passed(self) -> bool:
        now = time.time()

        async with self.lock:
            if self.target is None:
                self.target = now + self.interval
                return False

            if now >= self.target:
                self.target = now + self.interval
                return True

            return False
'''
trdtimer = FixedTimer(100)
pubtimer = FixedTimer(120)
pritimer = FixedTimer(140)
'''
'''
class WSClient:
    def __init__(self):
        self.ws = None
        self.send_q = asyncio.Queue(maxsize=2000)
        self.writer_task = None

    async def start(self, ws):
        self.ws = ws
        self.writer_task = asyncio.create_task(self._writer(), name="ws_writer")

    async def _writer(self):
        while True:
            payload = await self.send_q.get()
            try:
                await self.ws.send(payload)
            except Exception as e:
                # if send fails, you probably want to reconnect logic elsewhere
                # but at least don't silently die
                # (avoid awaiting logging if you are in shutdown)
                raise
            finally:
                self.send_q.task_done()

    async def send(self, message):
        payload = orjson.dumps(message)
        # Backpressure policy choice:
        #  - await put() to slow producers
        #  - or put_nowait() and drop on overflow
        await self.send_q.put(payload)

    async def send2(self, message, timeout=1.0):
        payload = orjson.dumps(message)
        await asyncio.wait_for(self.send_q.put(payload), timeout=timeout)
'''
trd_restart = 0
class KrakenTradesWS:
    '''
    __slots__ = (
                    'uri','subscription_queues','subscription_tasks','ws','is_running',
                    'retrys','subscribed_symbols','InstrumentDict','is_restart','start_time',
                    'has_sub','trades_db','trades_vol_count','window_seconds','buy_deque',
                    'sell_deque','total_buy_usd','total_sell_usd', 'inflow_usd', 'trade_id_tracker',
                    'trade_filter'
                )
    '''
    def __init__(self):
        self.uri = "wss://ws.kraken.com/v2"
        self.subscription_queues = {}
        self.subscription_tasks = {}
        self.ws = None
        self.is_running = False
        self.retrys = 0  # keep if you use it elsewhere
        self.subscribed_symbols = set()
        self.InstrumentDict = {}
        self.is_restart = False

        self.start_time = time.time()
        
        self.has_sub = False
        self._has_sub_event = asyncio.Event()   #FIX: no busy-loop until subscribed


        self.trades_db = defaultdict(list)  
        self.trades_vol_count = {}

        self.window_seconds = interval_seconds
        self.buy_deque = defaultdict(deque)        # symbol -> deque of (ts, usd)
        self.sell_deque = defaultdict(deque)       # symbol -> deque of (ts, usd)
        self.total_buy_usd = defaultdict(float)    # symbol -> float
        self.total_sell_usd = defaultdict(float)   # symbol -> float
        self.inflow_usd = {}

        #self.active_trade_ids = set() #for other brokers consider if ids are unique and not reused by other symbols

        self.active_trade_ids: dict[str, int] = {}  # trade_id -> refcount
        self._trade_lock = asyncio.Lock()
        self.datenow = datenow()

        self.out_q = asyncio.Queue(maxsize=200_000)
        self.writer_task = None

        self.in_q = asyncio.Queue(maxsize=200_000)
        self.consumer_task = None

        self.send_q = asyncio.Queue(maxsize=50_000)
        self.send_task = None
    '''
    async def subscribe(self, payload):
        await self.ws.send(orjson.dumps(payload))
        self.has_sub = True
    '''

    async def send(self, payload: dict) -> None:
        data = orjson.dumps(payload)
        try:
            self.out_q.put_nowait(data)
        except asyncio.QueueFull:
            # drop oldest to keep pipeline moving
            try:
                _ = self.out_q.get_nowait()
                self.out_q.task_done()
            except asyncio.QueueEmpty:
                pass
            try:
                self.out_q.put_nowait(data)
            except asyncio.QueueFull:
                pass

    async def _writer_loop(self, ws):
        while True:
            data = await self.out_q.get()
            try:
                await ws.send(data)

            finally:
                self.out_q.task_done()

    async def _consumer_loop(self):
        while True:
            raw = await self.in_q.get()
            try:
                message = orjson.loads(raw)
                if ("channel" in message) and message["channel"] == "trade" and message.get("data"):
                    # NOTE: calculate_inflows already tries to keep awaits outside locks
                    await self.calculate_inflows(message)
                elif "error" in message:
                    await self.on_error(message)
            except Exception as e:
                await system_log(f"{e.__traceback__.tb_lineno} {e}", "EXCEPTION   ")
            finally:
                self.in_q.task_done()

    async def subscribe(self, payload: dict):
        #await self.send(payload)
        self.send_q.put_nowait(orjson.dumps(payload))
        self.has_sub = True
        self._has_sub_event.set()

    async def trades_sub(self):
        new_symbols = set(instrument_dict) - self.subscribed_symbols
        if not new_symbols:
            return

        symbols = list(new_symbols)
        chunk_size = 200

        for i in range(0, len(symbols), chunk_size):
            sub_pairs = symbols[i:i + chunk_size]
            payload   = {
                "method": "subscribe",
                "params": {
                    "channel": "trade",
                    "symbol": sub_pairs,
                    "snapshot": True,
                },
            }
            await system_log(f"Trades: {', '.join(sub_pairs)}", "SUBSCRIPTION")
            await self.subscribe(payload)

        self.subscribed_symbols.update(new_symbols)

    def _id_add(self, trade_id: str) -> None:
        self.active_trade_ids[trade_id] = self.active_trade_ids.get(trade_id, 0) + 1

    def _id_discard(self, trade_id: str) -> None:
        c = self.active_trade_ids.get(trade_id)
        if c is None:
            return
        if c <= 1:
            self.active_trade_ids.pop(trade_id, None)
        else:
            self.active_trade_ids[trade_id] = c - 1

    def _id_contains(self, trade_id: str) -> bool:
        return trade_id in self.active_trade_ids

    def rebuild_active_trade_ids(self) -> None:
        ids: dict[str, int] = {}
        for dq in self.buy_deque.values():
            for _, _, tid in dq:
                ids[tid] = ids.get(tid, 0) + 1
        for dq in self.sell_deque.values():
            for _, _, tid in dq:
                ids[tid] = ids.get(tid, 0) + 1
        self.active_trade_ids = ids

    def _counts_match(self) -> bool:
        dq_count = 0
        for dq in self.buy_deque.values():
            dq_count += len(dq)
        for dq in self.sell_deque.values():
            dq_count += len(dq)

        id_count = sum(self.active_trade_ids.values())
        return dq_count == id_count

    async def calculate_inflows2(self, msg):
        async with self._trade_lock:
            for message in msg["data"]:
                try:
                    trade_id = message["trade_id"]
                    if self._id_contains(trade_id):
                        continue  # already represented in deques

                    side   = message["side"]
                    symbol = message["symbol"]

                    price = float(message["price"])
                    qty   = float(message["qty"])
                    usd   = price * qty

                    ts = datetime.strptime(
                        message["timestamp"][:-1], "%Y-%m-%dT%H:%M:%S.%f"
                    ).replace(tzinfo=timezone.utc).timestamp()

                    cutoff_now = time.time() - interval_seconds

                    buy_dq  = self.buy_deque[symbol]
                    sell_dq = self.sell_deque[symbol]
                    total_buy  = self.total_buy_usd[symbol]
                    total_sell = self.total_sell_usd[symbol]

                    # ---- ATOMIC ADD (exception safe) ----
                    self._id_add(trade_id)
                    try:
                        if side == "buy":
                            buy_dq.append((ts, usd, trade_id))
                            total_buy += usd
                        else:
                            sell_dq.append((ts, usd, trade_id))
                            total_sell += usd
                    except Exception:
                        # rollback id if deque append failed
                        self._id_discard(trade_id)
                        raise

                    # ---- PRUNE (deque pop always paired with id discard) ----
                    while buy_dq and buy_dq[0][0] < cutoff_now:
                        _, old_usd, old_id = buy_dq.popleft()
                        self._id_discard(old_id)
                        total_buy -= old_usd

                    while sell_dq and sell_dq[0][0] < cutoff_now:
                        _, old_usd, old_id = sell_dq.popleft()
                        self._id_discard(old_id)
                        total_sell -= old_usd

                    self.total_buy_usd[symbol]  = total_buy
                    self.total_sell_usd[symbol] = total_sell

                    inflow_usd = total_buy - total_sell
                    self.inflow_usd[symbol] = inflow_usd if inflow_usd > 0 else 0.0

                    if symbol in candlesDict:
                        candlesDict[symbol].inflow = self.inflow_usd[symbol]

                    #global pending_events, currranks_set
                    #if symbol in currranks_set | set(osd.order_state_dict['buy_pending'] + osd.order_state_dict['sell_allowed'] + osd.order_state_dict['sell_pending']):
                    #    await sl.update(symbol, inflow_usd)
                    #    await pending_events.put(1)

                except Exception as e:
                    await system_log(f"{e.__traceback__.tb_lineno} {e}", "EXCEPTION   ")
            if not self._counts_match():
                self.rebuild_active_trade_ids()
         
    async def calculate_inflows(self, msg):
        # ---- parse outside locks ----
        cutoff_now = time.time() - interval_seconds

        grouped = defaultdict(list)  # symbol -> list[(ts, usd, trade_id, side)]
        for m in msg["data"]:
            try:
                trade_id = m["trade_id"]
                symbol   = m["symbol"]
                side     = m["side"]

                price = float(m["price"])
                qty   = float(m["qty"])
                usd   = price * qty

                ts = datetime.strptime(
                    m["timestamp"][:-1], "%Y-%m-%dT%H:%M:%S.%f"
                ).replace(tzinfo=timezone.utc).timestamp()

                grouped[symbol].append((ts, usd, trade_id, side))
            except Exception as e:
                await system_log(f"{e.__traceback__.tb_lineno} {e}", "EXCEPTION   ")

        # ---- side effects to run after locks ----
        to_sl_update = []
        event_count = 0

        # If you need the watch set, compute once
        watch = (currranks_set | set(
            osd.order_state_dict["buy_pending"]
            + osd.order_state_dict["sell_allowed"]
            + osd.order_state_dict["sell_pending"]
        ))

        # ---- lock once per symbol (or per symbol-lock; see option 2) ----
        for symbol, trades in grouped.items():
            async with self._trade_lock:
                buy_dq  = self.buy_deque[symbol]
                sell_dq = self.sell_deque[symbol]
                total_buy  = self.total_buy_usd[symbol]
                total_sell = self.total_sell_usd[symbol]

                for ts, usd, trade_id, side in trades:
                    if self._id_contains(trade_id):
                        continue

                    self._id_add(trade_id)
                    try:
                        if side == "buy":
                            buy_dq.append((ts, usd, trade_id))
                            total_buy += usd
                        else:
                            sell_dq.append((ts, usd, trade_id))
                            total_sell += usd
                    except Exception:
                        self._id_discard(trade_id)
                        raise

                # prune once per symbol
                while buy_dq and buy_dq[0][0] < cutoff_now:
                    _, old_usd, old_id = buy_dq.popleft()
                    self._id_discard(old_id)
                    total_buy -= old_usd

                while sell_dq and sell_dq[0][0] < cutoff_now:
                    _, old_usd, old_id = sell_dq.popleft()
                    self._id_discard(old_id)
                    total_sell -= old_usd

                self.total_buy_usd[symbol] = total_buy
                self.total_sell_usd[symbol] = total_sell

                inflow_usd = total_buy - total_sell
                inflow_pos = inflow_usd if inflow_usd > 0 else 0.0
                self.inflow_usd[symbol] = inflow_pos

                # update candle inflow (consider doing this outside trade lock if candle has its own lock)
                if symbol in candlesDict:
                    candlesDict[symbol].inflow = inflow_pos

                should_signal = symbol in watch

            # ---- outside lock ----
            if should_signal:
                to_sl_update.append((symbol, inflow_usd))
                event_count += 1

        # ---- outside all locks: awaits ----
        for symbol, inflow_usd in to_sl_update:
            await sl.update(symbol, inflow_usd)
        #for _ in range(event_count):
        #    await pending_events.put(1)

        # keep rebuild under lock if it touches shared structures
        async with self._trade_lock:
            if not self._counts_match():
                self.rebuild_active_trade_ids()
    '''
    async def calculate_inflows(self, msg):
        for message in msg["data"]:
            try:
                #print('message',message)

                trade_id = message["trade_id"]

                #async with lock_manager.acquire(symbol):
                if trade_id in self.active_trade_ids:
                    continue                

                self.active_trade_ids.add(trade_id)

                side     = message["side"]
                symbol   = message["symbol"]

                # Use per-symbol persistent state
                buy_dq = self.buy_deque[symbol]
                sell_dq = self.sell_deque[symbol]
                total_buy = self.total_buy_usd[symbol]
                total_sell = self.total_sell_usd[symbol]

                # Minimal parsing, no intermediate objects
                price = float(message["price"])
                qty = float(message["qty"])
                usd = price * qty

                cutoff_now = time.time() - interval_seconds

                ts = datetime.strptime(
                    message["timestamp"][:-1], "%Y-%m-%dT%H:%M:%S.%f"
                ).replace(tzinfo=timezone.utc).timestamp()

                if side == "buy":
                    buy_dq.append((ts, usd, trade_id))
                    total_buy += usd
                else:
                    sell_dq.append((ts, usd, trade_id))
                    total_sell += usd

                # Wall-clock cleanup (precision guard)
                while buy_dq and buy_dq[0][0] < cutoff_now:
                    old_trade_id = buy_dq[0][2]
                    self.active_trade_ids.remove(old_trade_id)
                    total_buy -= buy_dq.popleft()[1]
                while sell_dq and sell_dq[0][0] < cutoff_now:
                    old_trade_id = sell_dq[0][2]
                    self.active_trade_ids.remove(old_trade_id)
                    total_sell -= sell_dq.popleft()[1]

                # Store updated totals back
                self.total_buy_usd[symbol]  = total_buy
                self.total_sell_usd[symbol] = total_sell

                inflow_usd = total_buy - total_sell
            
                if inflow_usd > 0:
                    self.inflow_usd[symbol] = inflow_usd
                else:
                    self.inflow_usd[symbol] = 0.0
              
                if inflow_usd >= 0 and symbol in candlesDict:
                    candlesDict[symbol].inflow = inflow_usd

            except Exception as e:                           
                await system_log(f"{e.__traceback__.tb_lineno} {e}", "EXCEPTION    ")
    '''
    def _put_latest(self, payload: dict) -> bool:
        try:
            self.send_q.put_nowait(orjson.dumps(payload))
            return True
        except asyncio.QueueFull:
            # drop oldest, then try once more
            try:
                _ = self.send_q.get_nowait()
                self.send_q.task_done()
            except asyncio.QueueEmpty:
                pass
            try:
                self.send_q.put_nowait(orjson.dumps(payload))
                return True
            except asyncio.QueueFull:
                return False

    async def _send_loop(self, ws):
        while True:
            data = await self.send_q.get()
            try:
                await ws.send(data)
            finally:
                self.send_q.task_done()

    async def on_open(self, ws):
        self.ws = ws
        self.is_running = True
        if self.send_task is None or self.send_task.done():
            self.send_task = asyncio.create_task(self._send_loop(ws))

        await ws_status.set_trades(1) 
        await system_log("TRD WS connected ", "CONNECTED   ")

        self.writer_task = asyncio.create_task(self._writer_loop(ws))
        self.consumer_task = asyncio.create_task(self._consumer_loop())

        self.has_sub = False
        self._has_sub_event.clear()

    async def on_message(self, message, ws):             #<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<    
        try:
            
            message = orjson.loads(message)
            if ('channel' in message) and message["channel"] == "trade" and message["data"]:
                await self.calculate_inflows(message)
            elif 'error' in message:
                self.on_error(message)

        except Exception as e:
            await system_log(f"{e.__traceback__.tb_lineno} {e}","EXCEPTION   ")

    async def on_close(self):
        self.is_running = False
        await ws_status.set_trades(0)
        
        if self.send_task and not self.send_task.done():
            self.send_task.cancel()
            await asyncio.gather(self.send_task, return_exceptions=True)
        self.send_task = None
        self.ws = None

        for task in list(self.subscription_tasks.values()):
            if not task.done():
                task.cancel()
        if self.subscription_tasks:
            await asyncio.gather(*self.subscription_tasks.values(), return_exceptions=True)

        self.subscription_queues.clear()
        self.subscription_tasks.clear()
       
        if self.consumer_task and not self.consumer_task.done():
            self.consumer_task.cancel()
            await asyncio.gather(self.consumer_task, return_exceptions=True)
        self.consumer_task = None

        if self.writer_task and not self.writer_task.done():
            self.writer_task.cancel()
            await asyncio.gather(self.writer_task, return_exceptions=True)
        self.writer_task = None

        # optional drains (prevents old msgs applying after reconnect)
        while not self.in_q.empty():
            try:
                _ = self.in_q.get_nowait()
                self.in_q.task_done()
            except asyncio.QueueEmpty:
                break

        while not self.out_q.empty():
            try:
                _ = self.out_q.get_nowait()
                self.out_q.task_done()
            except asyncio.QueueEmpty:
                break

        self.ws = None

    async def on_error(self, error):
        await system_log(f"TRDS WebSocket error: {error}", "WS TRD ERROR")

    async def send_kraken_ping(self, ws):
        while self.is_running:
            try:
                await ws.send(orjson.dumps({"method": "ping"})) #<-----------------------------
                await asyncio.sleep(10)
            except Exception as e:                    
                await system_log(f"Ping failed: {e}", "TRD PING ERR")
                await asyncio.sleep(1)
                break

    async def run(self):
        if sort_option == "ret":
            return
        delay = None
        while True:
            try:             
                async with websockets.connect(self.uri, ping_interval=20, ping_timeout=10, close_timeout=10, max_size=None) as ws:
                    await self.on_open(ws)

                    while self.is_running and not self._has_sub_event.is_set():
                        if instrument_dict:
                            await self.trades_sub()
                        # small sleep to yield; no busy spin
                        await asyncio.sleep(0.05)

                    while self.is_running: 
                        try:
                            raw = await ws.recv()

                            try:
                                self.in_q.put_nowait(raw)
                            except asyncio.QueueFull:
                                # drop oldest raw message to keep current flowing
                                try:
                                    _ = self.in_q.get_nowait()
                                    self.in_q.task_done()
                                except asyncio.QueueEmpty:
                                    pass
                                try:
                                    self.in_q.put_nowait(raw)
                                except asyncio.QueueFull:
                                    pass

                            # keep subscriptions up to date
                            if instrument_dict:
                                await self.trades_sub()
                            #if await trdtimer.passed():
                            #    raise
                        except websockets.exceptions.ConnectionClosed as e:
                            await ws_status.set_trades(0)
                            await system_log(f"{e.__traceback__.tb_lineno} TRDS WS inner error: Connection Closed Exception - {e}", "DISCONNECTED")
                            #await asyncio.sleep(1)
                            break
                        except websockets.ConnectionClosed:
                            await ws_status.set_trades(0)
                            await system_log(f"{e.__traceback__.tb_lineno} TRDS WS inner error: Connection Closed Timeout - {e}", "DISCONNECTED")
                            #await asyncio.sleep(1)
                            break
                        except Exception as e:
                            await ws_status.set_trades(0)
                            await system_log(f"{e.__traceback__.tb_lineno} TRDS WS inner error: {e}", "DISCONNECTED")
                            #await asyncio.sleep(1)
                            break

                        if list(instrument_dict.keys()):
                            await self.trades_sub()

            except Exception as e:
                await ws_status.set_trades(0)
                await system_log(f"{e.__traceback__.tb_lineno} TRDS WS outer error: {e}", "DISCONNECTED")
                #await asyncio.sleep(1)
            finally:
                await self.on_close()
                self.subscribed_symbols.clear()
                self.has_sub = False
                self.is_restart = True

                current_time = time.time()
                elapsed = current_time - self.start_time
        
                if elapsed >= 5.0:
                    self.start_time = current_time  # Reset timer
                    await system_log("TRDS WS closed – restarting in 5s", "RESTARTING  ")
                    delay = None
                    await asyncio.sleep(5)
                else:
                    delay = 5 if delay is None else min(delay + 5, 60)
                    await system_log(f"TRDS WS closed – restarting in {delay}s...", "RESTARTING  ")                   
                    await asyncio.sleep(delay)
                global trd_restart  
                if self.datenow != datenow():
                    trd_restart = 0
                    self.datenow = datenow()
                else:                
                    trd_restart += 1 if self.is_restart else 0
                
# ----------------------------------------------------------------------
#  PUBLIC WS  (independent restart)
# ----------------------------------------------------------------------
pub_restart = 0
class KrakenPublicWS:
    '''
    __slots__ = (
                    'uri','subscription_queues','subscription_tasks','ws',
                    'is_running','retrys','is_restart','start_time', 
                )
    '''
    def __init__(self):
        self.uri = "wss://ws.kraken.com/v2"
        self.subscription_queues = {}
        self.subscription_tasks = {}
        self.ws = None
        self.is_running = False
        self.retrys = 0  # keep if you use it elsewhere
        #self.TickerSubList = []
        #self.InstrumentDict = {}
        self.is_restart = False
        self.start_time = time.monotonic()

        self.ready_symbols = asyncio.Queue(maxsize=50_000)  # symbols scheduled for processing
        self._inflight = set()                             # symbols currently being processed
        self._workers = []                                 # worker tasks
        self._worker_count = 8                             # tune (CPU cores / load)
        self.datenow = datenow()

        self.out_q = asyncio.Queue(maxsize=100_000)
        self.writer_task = None

        self.non_ticker_q = asyncio.Queue(maxsize=50_000)
        self.non_ticker_task = None
    '''
    async def subscribe(self, ws, subscription):
        await ws.send(orjson.dumps(subscription))
    '''
    async def send(self, payload: dict) -> None:
        data = orjson.dumps(payload)
        try:
            self.out_q.put_nowait(data)
        except asyncio.QueueFull:
            # drop oldest to keep latest traffic moving
            try:
                _ = self.out_q.get_nowait()
            except asyncio.QueueEmpty:
                pass
            try:
                self.out_q.put_nowait(data)
            except asyncio.QueueFull:
                pass

    async def _writer_loop(self, ws):
        while True:
            data = await self.out_q.get()
            try:
                await ws.send(data)
            finally:
                self.out_q.task_done()

    async def _non_ticker_loop(self):
        while True:
            msg = await self.non_ticker_q.get()
            try:
                await Process_Public_Message(msg)
            except Exception as e:
                await system_log(f"{e}", "ERROR       ")
                await asyncio.sleep(0)
            finally:
                self.non_ticker_q.task_done()

    async def on_open(self, ws):
        self.ws = ws
        self.is_running = True
        
        await ws_status.set_public(1)        
        await system_log("Public WS connected", "CONNECTED   ")
        '''
        if self.writer_task is None or self.writer_task.done():
            self.writer_task = asyncio.create_task(self._writer_loop(ws))
        '''

        if getattr(self, "writer_task", None) and not self.writer_task.done():
            self.writer_task.cancel()
            await asyncio.gather(self.writer_task, return_exceptions=True)

        self.writer_task = asyncio.create_task(self._writer_loop(ws))

        if self.non_ticker_task is None or self.non_ticker_task.done():
            self.non_ticker_task = asyncio.create_task(self._non_ticker_loop())


        #global instrument_dict, subList
        #instrument_dict = {}

        subs = [{
                    "method" : "subscribe",
                    "params" : {"channel": "instrument"}
                }]
        for sub in subs:
            await self.send(sub)

        #asyncio.create_task(self.send_kraken_ping(ws))

        if not self._workers:
            self._workers = [asyncio.create_task(self._symbol_worker()) for _ in range(self._worker_count)]

    async def _symbol_worker(self):
        while True:
            sym = await self.ready_symbols.get()
            try:
                q = self.subscription_queues.get(sym)
                if q is None:
                    continue

                # Drain to the latest message (queue is maxsize=1, but drain anyway)
                msg = None
                while True:
                    try:
                        msg = q.get_nowait()
                        q.task_done()
                    except asyncio.QueueEmpty:
                        break

                if msg is not None:
                    await Process_Public_Message(msg)

            except Exception as e:
                await system_log(f"{e}", "ERROR       ")
                await asyncio.sleep(0)

            finally:
                # If new msg arrived while processing, reschedule symbol
                q = self.subscription_queues.get(sym)
                if q is not None and not q.empty():
                    try:
                        self.ready_symbols.put_nowait(sym)
                    except asyncio.QueueFull:
                        # if ready queue is full, just drop reschedule; the next on_message will re-add
                        self._inflight.discard(sym)

                else:
                    self._inflight.discard(sym)

                self.ready_symbols.task_done()
            
    async def on_message(self, raw):
        if not self.is_running:
            return

        try:
            message = orjson.loads(raw)

            # ---- original tolerant routing logic (yours) ----
            subscription = (
                message["channel"] if "channel" in message and message["channel"] != "ticker" else
                message["data"][0]["symbol"] if "channel" in message and message["channel"] == "ticker" and message.get("data") else
                message["method"] if "method" in message else
                "error" if "error" in message else None
            )

            if subscription is None:
                return

            if subscription == "error":
                await self.on_error(message)
                return
            '''
            # ---- non-ticker: process immediately (keeps your original tolerance) ----
            if message.get("channel") != "ticker":
                await Process_Public_Message(message)
                return
            '''

            if message.get("channel") != "ticker":
                try:
                    self.non_ticker_q.put_nowait(message)
                except asyncio.QueueFull:
                    # drop oldest non-ticker msg
                    try:
                        _ = self.non_ticker_q.get_nowait()
                    except asyncio.QueueEmpty:
                        pass
                    try:
                        self.non_ticker_q.put_nowait(message)
                    except asyncio.QueueFull:
                        pass
                return

            # ---- ticker: per-symbol serialization via queue (size=1) + worker pool ----
            # Guard: ticker messages can sometimes arrive without a symbol/data on reconnect edges
            data0 = (message.get("data") or [None])[0] or {}
            symbol = data0.get("symbol")
            if not symbol:
                '''
                await Process_Public_Message(message)
                return
                '''
                # route weird edges to non-ticker queue
                try:
                    self.non_ticker_q.put_nowait(message)
                except asyncio.QueueFull:
                    pass
                return


            # Ensure per-symbol queue exists (NO KeyError path)
            queue = self.subscription_queues.get(symbol)
            if queue is None:
                queue = asyncio.Queue(maxsize=1)
                self.subscription_queues[symbol] = queue

            # Keep only the latest message for this symbol
            if queue.full():
                try:
                    queue.get_nowait()
                    queue.task_done()
                except asyncio.QueueEmpty:
                    pass

            try:
                queue.put_nowait(message)
            except asyncio.QueueFull:
                # if it raced full again, just drop this tick
                pass

            # Schedule symbol once (guarantees 1 in-flight per symbol)
            if symbol not in self._inflight:
                self._inflight.add(symbol)
                try:
                    self.ready_symbols.put_nowait(symbol)
                except asyncio.QueueFull:
                    self._inflight.discard(symbol)

        except Exception as e:
            # match your existing error style
            await ws_status.set_public(0)
            await system_log(f"{e.__traceback__.tb_lineno} Public WS inner error: {e}", "DISCONNECTED")
            await asyncio.sleep(0)
    '''
    async def process_subscription_queue(self, subscription, queue):
        try:
            while True:
                message = await queue.get()
                try:
                    await Process_Public_Message(message)
                except Exception as e:
                    await system_log(f"{e}", "ERROR       ")
                    await asyncio.sleep(1)
                finally:                   
                    queue.task_done()
        except asyncio.CancelledError:
            while not queue.empty():
                queue.get_nowait()
                queue.task_done()
            raise
    '''
    async def on_close(self):
        self.is_running = False
        await ws_status.set_public(0)

        for task in list(self.subscription_tasks.values()):
            if not task.done():
                task.cancel()
        if self.subscription_tasks:
            await asyncio.gather(*self.subscription_tasks.values(), return_exceptions=True)

        self.subscription_queues.clear()
        self.subscription_tasks.clear()
        '''
        if self.writer_task and not self.writer_task.done():
            self.writer_task.cancel()
            await asyncio.gather(self.writer_task, return_exceptions=True)
        self.writer_task = None
        '''

        if getattr(self, "writer_task", None):
            self.writer_task.cancel()
            await asyncio.gather(self.writer_task, return_exceptions=True)
            self.writer_task = None

        if self.non_ticker_task and not self.non_ticker_task.done():
            self.non_ticker_task.cancel()
            await asyncio.gather(self.non_ticker_task, return_exceptions=True)
        self.non_ticker_task = None

        self.ws = None

        for t in self._workers:
            if not t.done():
                t.cancel()
        if self._workers:
            await asyncio.gather(*self._workers, return_exceptions=True)
        self._workers.clear()
        self._inflight.clear()

        # (optional) drain ready_symbols queue
        while not self.ready_symbols.empty():
            try:
                self.ready_symbols.get_nowait()
                self.ready_symbols.task_done()
            except asyncio.QueueEmpty:
                break

        while not self.non_ticker_q.empty():
            try:
                self.non_ticker_q.get_nowait()
                self.non_ticker_q.task_done()
            except asyncio.QueueEmpty:
                break

        while not self.out_q.empty():
            try:
                self.out_q.get_nowait()
                self.out_q.task_done()
            except asyncio.QueueEmpty:
                break

    async def on_error(self, error):
        await system_log(f"Public WebSocket error: {error}", "WS PUB ERROR")

    async def send_kraken_ping(self, ws):
        while self.is_running:
            try:
                await ws.send(orjson.dumps({"method": "ping"}))
                await asyncio.sleep(15)
            except Exception as e:                    
                await system_log(f"Ping failed: {e}", "PUB PING ERR")
                await asyncio.sleep(1)
                break

    async def run(self):
        delay = None
        while True:
            try:
                async with websockets.connect(self.uri, ping_interval=20, ping_timeout=10, close_timeout=10, max_size=2**20) as ws:
                    await self.on_open(ws)
                    while self.is_running:
                        try:
                            message = await ws.recv()
                            await self.on_message(message)
                            #if await pubtimer.passed():
                            #    raise
                        except websockets.exceptions.ConnectionClosed as e:
                            await ws_status.set_public(0)
                            await system_log(f"{e.__traceback__.tb_lineno} Public WS inner error: Connection Closed Exception - {e}", "DISCONNECTED")
                            await asyncio.sleep(1)
                            break
                        except websockets.ConnectionClosed as e:
                            await ws_status.set_public(0)
                            await system_log(f"{e.__traceback__.tb_lineno} Public WS inner error: Connection Closed Timeout - {e}", "DISCONNECTED")
                            await asyncio.sleep(1)
                            break
                        except Exception as e:
                            await ws_status.set_public(0)
                            await system_log(f"{e.__traceback__.tb_lineno} Public WS inner error: {e}", "DISCONNECTED")
                            await asyncio.sleep(1)
                            break                 
            except Exception as e:
                await ws_status.set_public(0)
                await system_log(f"{e.__traceback__.tb_lineno} Public WS outer error: {e}", "DISCONNECTED")
                await asyncio.sleep(1)
            finally:
                await self.on_close()
                self.is_restart = True

                current_time = time.monotonic()
                elapsed = current_time - self.start_time
        
                if elapsed >= 5.0:
                    self.start_time = current_time  # Reset timer
                    await system_log("Public WS closed – restarting now", "RESTARTING  ")
                    delay = None
                    await asyncio.sleep(5)
                else:
                    delay = 5 if delay is None else min(delay + 5, 60)
                    await system_log(f"Public WS closed – restarting in {delay}s...", "RESTARTING   ")                  
                    await asyncio.sleep(delay)
                global pub_restart   
                if self.datenow != datenow():
                    pub_restart = 0
                    self.datenow = datenow()
                else:
                    pub_restart += 1 if self.is_restart else 0
                
# ----------------------------------------------------------------------
#  PRIVATE WS  (independent restart)
# ----------------------------------------------------------------------
pri_restart = 0
class KrakenPrivateWS:
    __slots__ = (
                    'uri','ws','pri_ws_token','lock',
                    'retrys','is_restart','start_time','datenow',
                    'out_q','writer_task',
                )
    def __init__(self):
        self.uri = "wss://ws-auth.kraken.com/v2"
        self.ws = None
        self.pri_ws_token = None
        self.lock = asyncio.Lock()
        self.retrys = 0  # keep if used
        self.is_restart = False
        self.start_time = time.monotonic()
        self.datenow = datenow()
        self.out_q = asyncio.Queue(maxsize=50_000)
        self.writer_task = None

    async def __pri_ws_token__(self):
        '''
        async with self.lock:
            self.pri_ws_token = kraken_request('/0/private/GetWebSocketsToken').json()['result']['token']
        '''
        async with self.lock:
            def _get_token():
                return kraken_request('/0/private/GetWebSocketsToken').json()['result']['token']
            self.pri_ws_token = await asyncio.to_thread(_get_token)
   
    async def send(self, payload: dict) -> None:
        # safe from any task, even during reconnect
        #await self.out_q.put(orjson.dumps(payload))
        try:
            self.out_q.put_nowait(orjson.dumps(payload))
            return True
        except asyncio.QueueFull:
            return False


    async def _writer_loop(self, ws):
        while True:
            data = await self.out_q.get()
            try:
                await ws.send(data)
            finally:
                self.out_q.task_done()

    async def on_open(self, ws):
        self.ws = ws
        await ws_status.set_private(1)
        await system_log("Private WS connected", "CONNECTED   ")
             
        if getattr(self, "writer_task", None) and not self.writer_task.done():
            self.writer_task.cancel()
            await asyncio.gather(self.writer_task, return_exceptions=True)

        # start writer
        self.writer_task = asyncio.create_task(self._writer_loop(ws))        

        balances_sub = {
            "method": "subscribe",
            "params": {
                "channel": "balances",
                "snapshot": True,
                "token": self.pri_ws_token
            }
        }
        executions_sub = {
            "method": "subscribe",
            "params": {
                "channel": "executions",
                "ratecounter": True,
                "snap_trades": True,
                "snap_orders": True,
                "order_status": True,
                "token": self.pri_ws_token
            }
        }
        for sub in [balances_sub, executions_sub]:           
            await self.send(sub)

        #asyncio.create_task(self.send_kraken_ping(ws))

    async def on_message(self, message):
        message = orjson.loads(message)
        await Process_Private_Message(message)

    async def on_close(self):
        await ws_status.set_private(0)

        if getattr(self, "writer_task", None):
            self.writer_task.cancel()
            await asyncio.gather(self.writer_task, return_exceptions=True)
            self.writer_task = None

        self.ws = None   
        
        await system_log("Private WebSocket Closed.", "CLOSED      ")

    async def on_error(self, error):
        await system_log(f"Private WebSocket error: {error}", "WS PRI ERROR")

    async def send_kraken_ping(self, ws):
        while self.ws is not None:
            try:
                await ws.send(orjson.dumps({"method": "ping"}))
                await asyncio.sleep(15)
            except Exception as e:
                await system_log(f"Ping failed: {e}", "PRI PING ERR")
                break

    async def run(self):
        """Independent loop: reconnects only itself on any failure."""
        delay = None
        while True:
            try:
                await self.__pri_ws_token__()
                async with websockets.connect(self.uri, ping_interval=20, ping_timeout=10, close_timeout=10, max_size=2**20) as ws:
                    await self.on_open(ws)
                    while self.ws is not None:
                        try:
                            message = await ws.recv()
                            await self.on_message(message)

                        except websockets.exceptions.ConnectionClosed as e:
                            await ws_status.set_private(0)
                            await system_log(f"{e.__traceback__.tb_lineno} Private WS inner error: Connection Closed Exception - {e}", "DISCONNECTED")
                            await asyncio.sleep(1)
                            break
                        except websockets.ConnectionClosed as e:
                            await ws_status.set_private(0)
                            await system_log(f"{e.__traceback__.tb_lineno} Private WS inner error: Connection Closed Timeout - {e}", "DISCONNECTED")
                            await asyncio.sleep(1)
                            break
                        except Exception as e:
                            await ws_status.set_private(0)
                            await system_log(f"{e.__traceback__.tb_lineno} Private WS inner error: {e}", "DISCONNECTED")
                            await asyncio.sleep(1)
                            break
            except Exception as e:
                await ws_status.set_private(0)
                await system_log(f"{e.__traceback__.tb_lineno} Private WS outer error: {e}", "DISCONNECTED")
                await asyncio.sleep(1)
            finally:
                await self.on_close()
                self.is_restart = True

                current_time = time.monotonic()
                elapsed = current_time - self.start_time
        
                if elapsed >= 5.0:
                    self.start_time = current_time  # Reset timer          
                    await system_log("Private WS closed – restarting now", "RESTARTING  ")
                    delay = None
                    await asyncio.sleep(5)
                else:  
                    delay = 5 if delay is None else min(delay + 5, 60)
                    await system_log(f"Private WS closed – restarting in {delay}s...", "RESTARTING  ")                   
                    await asyncio.sleep(delay)
                global pri_restart
                if self.datenow != datenow():
                    pri_restart = 0
                    self.datenow = datenow()
                else:
                    pri_restart += 1 if self.is_restart else 0                 
# ----------------------------------------------------------------------
#  Updated main: starts everything and runs forever (no restart loop)
# ----------------------------------------------------------------------
def datenow(): 
    return datetime.now().strftime("%d")

async def main(): 
    await system_log(f"Lock acquired, running the main {script_name} script", "LOCK SET    ")

    global instrument_dict, subList, public_ws, private_ws, trades_ws, pending_events
    #pending_events = asyncio.Queue()
    instrument_dict = {}

    public_ws  = KrakenPublicWS()
    private_ws = KrakenPrivateWS()
    trades_ws  = KrakenTradesWS()

    pub_task = asyncio.create_task(public_ws.run())
    pri_task = asyncio.create_task(private_ws.run())
    trades_task = asyncio.create_task(trades_ws.run())
    trader_task = asyncio.create_task(slot_trader())  

    try:
        await asyncio.gather(
                                pub_task,
                                pri_task,
                                trades_task,
                                trader_task,
                                return_exceptions=True,
                            )
    except KeyboardInterrupt:
        pub_task.cancel()
        pri_task.cancel()
        trades_task.cancel()
        trader_task.cancel()
        await asyncio.gather(pub_task, pri_task,  trades_task, trader_task, return_exceptions=True)

        await public_ws.on_close()
        await private_ws.on_close()

        await trades_ws.on_close()
    except Exception as e:                   
        await system_log(f"Main error: {e.__traceback__.tb_lineno} {e}", "ERROR       ")
    finally:
        # Clean up references
        public_ws  = None
        private_ws = None
        trades_ws  = None

# ----------------------------------------------------------------------
# NEW entry-point (replace the old `if __name__ == "__main__":` block)
# ----------------------------------------------------------------------
if __name__ == "__main__":
    lock_file = f"{script_name}.lock"
    lock = FileLock(lock_file)
    try:
        with lock.acquire(timeout=0): 
            controller_link.write('command', ('Run', 'Running'))
            try:
                asyncio.run(main())
                controller_link.cleanup()
            except Exception as e:                          
                asyncio.run(system_log(f"-------------> {e}", "ERROR       "))  
            asyncio.run(system_log("Lock released, main script stopped", "LOCK REL    "))
    except Timeout:
        controller_link.write('command', ('Stop', 'Stopped'))
        sys.exit(0)
