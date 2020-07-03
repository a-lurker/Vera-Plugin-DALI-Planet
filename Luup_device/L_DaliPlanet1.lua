--[[
    Originated by zoot1612, modified and updated by a-lurker, 29 Jan 2015; last update May 2019
    http://forum.micasaverde.com/index.php/topic,9677.msg201758.html#msg201758

    Suits the Creative Lighting DALI DidIO and Tridonic gateways.
    Vera <-- LAN/USB/RS232 --> DALI gateway <-- dali bus --> DALI devices

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    version 3 (GPLv3) as published by the Free Software Foundation;

    In addition to the GPLv3 License, this software is only for private
    or home useage. Commercial utilisation is not authorized.

    The above copyright notice and this permission notice shall be included
    in all copies or substantial portions of the Software.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
]]

local PLUGIN_NAME     = 'DaliPlanet'
local PLUGIN_SID      = 'urn:dali-org:serviceId:Dali1'
local PLUGIN_VERSION  = '0.55'
local THIS_LUL_DEVICE = nil
local PLUGIN_URL_ID   = 'al_dali_info'
local URL_ID          = './data_request?id=lr_'..PLUGIN_URL_ID

local GATEWAY_TYPE    = 0
local CL_DIDIO        = 1  -- Creative Lighting: 7 TX & 3 RX bytes
local TRIDONIC_SCI_1  = 2  -- RS232 PS/S (not default):  7 TX & 3 RX bytes - need to instruct hardware to use this mode
local TRIDONIC_SCI_2  = 3  -- RS232 PS/S (default)    :  5 TX & 5 RX bytes IMPLEMENTED BUT NOT TESTED

--[[
    Other gateway hardware worth investigating:
    Lunatone DALI RS232 SCI - rebranded Tridonic - refer Lunatone Cockpit software
    Wago 750-641, DALI/DSI Master Module
    GE Lighting:  DALI Type 2, SKU: 65324
    Embedded Systems DALI RS485
    Starfield RT03
    DALCNET DGM01-1248
    Helvar Digidim 503 AV RS232
]]

--------------------------------------------------------------------------------
-- setup global variables
local THIS_LUL_DEVICE     = nil
local DIMMABLE_LIGHT_DEV  = 'urn:schemas-upnp-org:device:DimmableLight:1'
local SWP_SID             = 'urn:upnp-org:serviceId:SwitchPower1'
local SWD_SID             = 'urn:upnp-org:serviceId:Dimming1'
local ENERGY_METERING_SID = 'urn:micasaverde-com:serviceId:EnergyMetering1'

local m_LightCount      = 0
local m_GroupCount      = 0
local m_UnpoweredCount  = 0
local m_UnpoweredLights = {}

local TWENTY_MINUTES      = 1200  -- in second intervals
local m_HeartBeatInterval = TWENTY_MINUTES
local m_HeartBeatEnable   = ''    -- is set to either: '0' or '1'

local m_Busy = false
local m_LastWasConfigCommand = false
local m_TimingInitPeriod = false

-- when first powered on, most new lights light up. So fade down first for instant gratification
local m_fadeUp = false

local rxMsgTable   = {}
local TASK_ERROR   = 2
local m_TaskHandle = -1

-- http://bitop.luajit.org/api.html
local bitFunctions = require('bit')

--[[

DALI background:

Maximum number of devices:  64
Number of Groups:           16
Number of Scenes per Group: 16

Short address  - a 6 bit number
Random Address - a 24 bit value that is mainly used for
sorting out short address conflicts when commissioning.
You can also address devices as a group.

DTR = Data Transfer Register. A value is broadcast to all devices, which is then retained in
the DTR of the device. A subsequent command can then direct that the DTR be transferred, into
a particular register, in a particular device.

]]

local DALI_YES = 0xFF  -- a reply of yes.  Tridonic may possibly use 0x01?

local DALI_MAX_LEVEL = 0xFE  -- max brightness is 254, not 255

-- DALI_MASK is used by:
-- DirectArcCommand   MASK stops any fading in progress (0 = fade down then off)
-- StoreDTRAsScene    MASK removes the device from the scene
-- RemoveFromScene    MASK is stored in the scene, same as above?
-- QueryActualLevel   MASK indicates a fault or lamp not ready
-- QuerySceneLevel    MASK indicates the device is not in the scene
-- QueryShortAddress  MASK indicates the device has no short address
local DALI_MASK = 0xFF

-- Equipment must respond to broadcast. The device don't need a short address
-- to do so. Collisions may occur and also the answer(s) may be 'No'.
local DALI_BROADCAST = 0xFF  -- broadcast address
local GROUP_OFFSET   = 64    -- group addresses are offset by this amount

--------------------------------------------------------------------------------
-- start of DALI commands
--------------------------------------------------------------------------------

-- misc commands
local DALI_LINK_CHECK       =  -2   -- see CheckGateway()
local DALI_DIRECT_ARC       =  -1   -- see DirectArcCommand()

--------------------------------------------------------------------------------
-- lshft(code, 1) OR'ed with S flag = 0x01
--------------------------------------------------------------------------------

-- MSB = YAAAAAAS;  LSB = command code
local DALI_OFF_NF           =   0   -- extinguish lamp without fading
local DALI_UP               =   1   -- dim up   for 200 ms (execution time) using the selected 'FADE RATE'
local DALI_DOWN             =   2   -- dim down for 200 ms (execution time) using the selected 'FADE RATE'
local DALI_STEP_UP          =   3   -- set actual arc power level one step higher without fading
local DALI_STEP_DOWN        =   4   -- set actual arc power level one step higher without fading
local DALI_R_MAX            =   5   -- recall max level
local DALI_R_MIN            =   6   -- recall min level
local DALI_DOWN_OFF         =   7   -- step down and off
local DALI_ON_UP            =   8   -- on and step up
local DALI_DAPC_SEQ         =   9   -- not implemented: v2 Direct Arc Power Cmd sequence
-- 10 to 15 = reserved
local DALI_GO_TO_SCENE      =  16   -- 0x10 to 0x1F   change scene

-- 32 to 128, 258 and 259 must be repeated within 100 msec in order to be executed
local DALI_RESET            =  32   -- reset parameters to default settings
local DALI_DTR_ACTUAL_LEV   =  33   -- store actual arc power level in the DTR without changing the current light intensity.
-- 34 to 41 = reserved
local DALI_DTR_MAX_LEV      =  42   -- save the value in DTR as new 'MAX LEVEL'.
local DALI_DTR_MIN_LEV      =  43   -- save the value in DTR as new 'MIN LEVEL'.
local DALI_DTR_SYS_FAIL_LEV =  44   -- save the value in DTR as new 'SYSTEM FAILURE LEVEL'.
local DALI_DTR_PWR_ON_LEV   =  45   -- save the value in DTR as new 'POWER ON LEVEL'
local DALI_DTR_FADE_TIME    =  46   -- set fade time to value in DTR. To use Extended Fade Time cmd; this value must by 0x00
local DALI_DTR_FADE_RATE    =  47   -- set fade rate to value in DTR
-- 48 to 63 = reserved
local DALI_ADD_SCENE_B      =  64   -- 0x40 to 0x4F  store the DTR as scene
local DALI_REMOVE_SCENE_B   =  80   -- 0x50 to 0x5F  remove from scene
local DALI_ADD_GROUP_B      =  96   -- 0x60 to 0x6F  add to group
local DALI_REMOVE_GROUP_B   = 112   -- 0x70 to 0x7F  remove from group
local DALI_DTR_S_ADDR       = 128   -- set Short Address to value in DTR: 0AAA AAA1 or 1111 1111 (DALI_MASK)
local DALI_EN_WR_MEM        = 129   -- not implemented: v2 enable write memory - sent before DALI_WR_MEM
-- 130 to 143 = reserved
local DALI_Q_STATUS         = 144   -- query status
local DALI_Q_BALLAST        = 145   -- ask if there is a ballast with the given address that is able to communicate.
local DALI_Q_LAMP_FAILURE   = 146   -- query lamp failure
local DALI_Q_LAMP_POWER_ON  = 147   -- query lamp power
local DALI_Q_LIMIT_ERROR    = 148   -- query if the last requested arc power level at the given address could not be met
local DALI_Q_RESET_STATE    = 149   -- query reset state
local DALI_Q_MISSING_SHORT  = 150   -- query lamp failure
local DALI_Q_VER_NUM        = 151   -- query software version
local DALI_Q_DTR_CONTENTS   = 152   -- query contents of DTR
local DALI_Q_TYPE           = 153   -- query device type
local DALI_Q_PHYS_MIN_LEV   = 154   -- query physical minimum level
local DALI_Q_POWER_FAILURE  = 155   -- query power failure
local DALI_Q_DTR1_CONTENTS  = 156   -- v2 query contents of DTR1
local DALI_Q_DTR2_CONTENTS  = 157   -- v2 query contents of DTR2
-- 158 to 159 = reserved
local DALI_Q_LEV            = 160   -- query actual light level
local DALI_Q_MAX            = 161   -- query max light level
local DALI_Q_MIN            = 162   -- query min light level
local DALI_Q_PWR_ON_LEV     = 163   -- query power on level
local DALI_Q_SYS_FAIL_LEV   = 164   -- query system failure level
local DALI_Q_FADE           = 165   -- query fade time / fade rate
-- 166 to 175 = reserved
local DALI_Q_SCENE_LEV_B    = 176   -- 0xB0 to 0xBF  query scene level
local DALI_Q_R_GRP_L        = 192   -- query group 0-7
local DALI_Q_R_GRP_H        = 193   -- query group 8-15
local DALI_Q_R_ADDR_H       = 194   -- query random address (H)
local DALI_Q_R_ADDR_M       = 195   -- query random address (M)
local DALI_Q_R_ADDR_L       = 196   -- query random address (L)
local DALI_RD_MEM           = 197   -- not implemented: v2 read memory; DTR1 == bank, DTR == location, DTR2 will contain the data
-- 198 to 223 = reserved
-- 224 to 254 = APPLICATION EXTENDED COMMANDS - manufacturer dependent!
-- For type 8?: commands 240 to 247 are sent twice within 100 ms to minimise config errors
local DALI_Q_VER_NUM_EXT    = 255   -- not implemented: v2 query extended version number
--------------------------------------------------------------------------------
-- MSB = command code;  LSB = various data
-- Special command: 101CCCC1 = 0xA0 or lshft(code-256, 1) or S flag = 0x01
-- Command is acted on by all slaves, as appropriate to the command and the slave's status
--------------------------------------------------------------------------------
local DALI_TERMINATE        = 256   -- terminate
local DALI_SET_DTR          = 257   -- store value in DTR
-- DALI_INIT data: 0x00 = all devices, 0xff = those with no short addresses
-- shrt/grp addr = just the one/those addressed (good for fixing duplicate addresses)
local DALI_INIT             = 258   -- initialise (repeat within 100 msec)
local DALI_RAND             = 259   -- randomise  (repeat within 100 msec)
local DALI_COMPARE          = 260   -- compare (DALI_RX_ERRORs are possible )
local DALI_WITH_DRAW        = 261   -- withdraw
-- 262 to 264 = reserved
local DALI_S_ADRR_H         = 264   -- search address H
local DALI_S_ADRR_M         = 265   -- search address M
local DALI_S_ADRR_L         = 266   -- search address L
local DALI_P_S_ADDR         = 267   -- program short address - only 'Selected' devices respond
local DALI_V_S_ADDR         = 268   -- verify short address
local DALI_Q_S_ADDR         = 269   -- query short address - only 'Selected' devices respond
local DALI_PHYS_SEL         = 270   -- physical selection
-- 271 = reserved
--------------------------------------------------------------------------------
-- Special command: 110CCCC1 = 0xC0 or lshft(code-256, 1) or S flag = 0x01
-- Command is acted on by all slaves, as appropriate to the command and the slave's status
--------------------------------------------------------------------------------
-- send 272 cmd plus device type. This alerts only those devices, that a extended cmd for them is
-- coming. Required when using broadcast or group addressing. Not required for short addressing
-- ie one only device, as we already know that it can only accept specific extended commands.
local DALI_EN_DEV_TYPE_X    = 272   -- not implemented: v2 value is the device type and enables usage of cmds 224 to 254
local DALI_SET_DTR1         = 273   -- v2 store value in DTR1 (not the same as DTR)
local DALI_SET_DTR2         = 274   -- v2 store value in DTR2
local DALI_WR_MEM           = 275   -- not implemented: v2 write memory
-- 276 to 349 = reserved

--------------------------------------------------------------------------------
-- some type 6 (LED) extended commands
local DALI_6_Q_FEATURES     = 240   -- query features
local DALI_6_Q_FAIL_STATUS  = 241   -- query failure status

--------------------------------------------------------------------------------
--[[ HACK
-- some type 8 (color) extended commands
local DALI_8_Q_FEATURES     = 24x   -- query features
local DALI_8_Q_FAIL_STATUS  = 24x   -- query failure status
]]
--------------------------------------------------------------------------------
-- end of DALI commands
--------------------------------------------------------------------------------
-- these vars hold config info used to accommodate different manufacturers. Refer to setGatewayType()
local IP_PORT    = 0
local LINK_CHK   = 0x00
local EXPECT_NR  = 0x00
local EXPECT_R   = 0x00
local buildTXmsg = nil
local RX_MSG_LEN = 0
local DALI_RX_INIT_OK     = 0x00
local DALI_RX_RESPONSE    = 0x00
local DALI_RX_NO_RESPONSE = 0x00
local DALI_RX_ERROR       = 0x00
local FIND_RESULT_BYTES   = 0
--------------------------------------------------------------------------------

-- don't change this, it won't do anything. Use the DebugEnabled flag instead
local DEBUG_MODE = false

local function debug(textParm, logLevel)
    if DEBUG_MODE then
        local text = ''
        local theType = type(textParm)
        if (theType == 'string') then
            text = textParm
        else
            text = 'type = '..theType..', value = '..tostring(textParm)
        end
        luup.log(PLUGIN_NAME..' debug: '..text,50)

    elseif (logLevel) then
        local text = ''
        if (type(textParm) == 'string') then text = textParm end
        luup.log(PLUGIN_NAME..' debug: '..text, logLevel)
    end
end

-- If non existent, create the variable
-- Update the variable only if needs to be
local function updateVariable(varK, varV, sid, id)
    if (sid == nil) then sid = PLUGIN_SID      end
    if (id  == nil) then  id = THIS_LUL_DEVICE end

    if (varV == nil) then
	    if (varK == nil) then
            luup.log(PLUGIN_NAME..' debug: '..'Error: updateVariable was supplied with nil values', 1)
		else
            luup.log(PLUGIN_NAME..' debug: '..'Error: updateVariable '..tostring(varK)..' was supplied with a nil value', 1)
		end
        return
    end

    local newValue = tostring(varV)
    debug(newValue..' --> '..varK)

    local currentValue = luup.variable_get(sid, varK, id)
    if ((currentValue ~= newValue) or (currentValue == nil)) then
        luup.variable_set(sid, varK, newValue, id)
    end
end

-- escape text chars to suit json
-- http://www.ietf.org/rfc/rfc4627.txt
local function escJSONentities(s)
    s = s:gsub('\\', '\\u005c')
    s = s:gsub('\n', '\\u000a')
    s = s:gsub('"',  '\\u0022')
    s = s:gsub("'",  '\\u0027')
    s = s:gsub('/',  '\\u002f')
    s = s:gsub('\t', '\\u0009')
    return s
end

local function escHTMLentities(s)
    s = s:gsub('&', '&amp;')
    s = s:gsub('<', '&lt;')
    s = s:gsub('>', '&gt;')
    s = s:gsub('"', '&quot;')
    s = s:gsub("'", '&#039;')
    return s
end

local function escHTMLentities2(s)
    s = s:gsub('&', '&#x26;')
    s = s:gsub('<', '&#x3c;')
    s = s:gsub('>', '&#x3e;')
    s = s:gsub('"', '&#x22;')
    s = s:gsub("'", '&#x27;')
    return s
end

local function htmlHeader()
return [[<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
    "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en">
<head>
<meta http-equiv="content-type" content="text/html; charset=utf-8"/>]]
end

local function htmlJavaScript()
    local javaScript = [[

var submitting = false;

function parseJson(jsonStr)
{
   var jsonObject = null;

   // got a native parser? If so use it
   if (window.JSON && (typeof JSON.parse === "function"))
   {
      try
      {
         //alert('Using native parser');
         jsonObject = JSON.parse(jsonStr);
      }
      catch(e1)
      {
         jsonObject = null;
         //alert('Error name = '+e1.name+', error message = '+e1.message+', jsonStr = '+jsonStr);
      }
   }
   else
   { alert('No JSON parser found - get a new browser!'); }

   return jsonObject;
}

function ajaxRequest(url, args, callBack)
{
   // keep it all local so we can make multiple
   // requests without confusion between them
   var httpRequest = false;

   if (window.XMLHttpRequest)
   {  // IE7, Mozilla, Safari, ...
      httpRequest = new XMLHttpRequest();
   }
   else if (window.ActiveXObject)
   {  // IE
      try { httpRequest = new ActiveXObject("Msxml2.XMLHTTP"); }
      catch (e1)
      {
         try { httpRequest = new ActiveXObject("Microsoft.XMLHTTP"); }
         catch (e2)
         {}
      }
   }

   if (!httpRequest)
   {
      alert('Cannot create httpRequest instance');
      return;
   }

   // the server's response will be screened by the handler and then passed on to the callBack function
   httpRequest.onreadystatechange = function() {
      if (httpRequest.readyState == 4)
      {
         if (httpRequest.status == 200) callBack(httpRequest);
         // the submission process is over
         submitting = false;
      }
      };

   var first = true;
   for (var prop in args) {
      if (first)
         { url += '?' + prop + '=' + args[prop]; first = false; }
      else
         url += '&' + prop + '=' + args[prop];
   }

   httpRequest.open('GET', url, true);
   httpRequest.send(null);
}

function getDeviceInfoCallBack(response)
{
   var jsonObj = parseJson(response.response);
   if (jsonObj && jsonObj.ballastInfo)
   {
      document.getElementById('deviceStatusID').innerHTML = jsonObj.ballastInfo;
      window.scrollTo(0,0);
      document.getElementById("daliAddressID").focus();
   }
}

// ----------------------------------------------------------------------------
// The "Submit" button was clicked
//
// Note that the submit button is of type "button", not type "submit"
// This disables submission of the form if javascript is not enabled.
// If the "submit" type button was used, the form could still be submitted
// without any validation being performed. We don't want that.
// ----------------------------------------------------------------------------

function submitClicked()
{
   // stop the form from being resubmitted, if the user gets a bit clicky, until we get a server response
   if (submitting) return false;

   // validate the DALI address
   var daliAddress = parseInt(document.getElementById("daliAddressID").value,10);
   if (isNaN(daliAddress) || (daliAddress < 0) || (daliAddress > 63))
      daliAddress = 'error';

   var URL_PART_A    = '/port_3480/data_request';
   var PLUGIN_URL_ID = 'al_dali_info';

   // send the DALI address to the server
   submitting = true;
   var args = {
     id:         'lr_'+PLUGIN_URL_ID,
     fnc:        'getDeviceInfo',
     daliAddress: daliAddress,
     random:      Math.random()
     };

   ajaxRequest(URL_PART_A, args, getDeviceInfoCallBack);

   // the button is not to perform any further actions
   return false;
}

function startUp() {
   document.getElementById("submitBtnID").onclick = submitClicked;
   document.getElementById("daliAddressID").focus();
}

// execute this
window.onload = startUp;

]]
   --return '<script type="text/javascript">'..escHTMLentities(javaScript)..'</script>'
   --return '<script type="text/javascript">'..escHTMLentities2(javaScript)..'</script>'
   return '<script type="text/javascript">'..javaScript..'</script>'
end

-- used to display message debug strings
local function byteArrayToHexString(byteArray)
    if (byteArray == nil) then debug ('byteArray is nil in byteArrayToHexString') return '' end

    local str = {}
    for i = 1, #byteArray do
        str[i] = string.format('%02X', byteArray[i])
    end
    return table.concat(str,',')
end

local function byteArrayToString(byteArray)
    if (byteArray == nil) then debug ('byteArray is nil in byteArrayToString') return '' end

    local str = {}
    for i = 1, #byteArray do
        local number = byteArray[i]
        if ((number < 0) or (number > 255)) then
            debug ('Error: number cannot be converted to char: '..number)
            return ''
        else
            str[i] = string.char(number)
        end
    end
    return table.concat(str)
end

-- the initialisation period timer has timed out
local function m_timerTimeoutInitPeriod(dummy)
    m_TimingInitPeriod = false
end

-- b is the boolean value. s is the string value
local function getBitMap(byte8, bitPosition)
    local bitMap = {}
    if (bitFunctions.band(byte8, 2^bitPosition) == 0) then
        bitMap = {b=false, s='0'}
    else
        bitMap = {b=true,  s='1'}
    end
    return bitMap
end

-- make an array containing a boolean result for each bit in the byte
local function getStatusFlags(byte8)
--[[
7  query: power failure:       0 = no or arc pwr has been rx'ed after last power on
6  query: missing short addr:  0 = no
5  query: reset state:         0 = no
4  fade:                       0 = ready, 1 = fade running
3  query: limit level:         0 = power level is between min max or off
2  lamp arc power on:          0 = off
1  lamp failure:               0 = OK
0  ballast status:             0 = OK
]]
    local stFlgs = {
    powerFailure     = getBitMap(byte8,7),
    missingShortAddr = getBitMap(byte8,6),
    resetState       = getBitMap(byte8,5),
    fadeReady        = getBitMap(byte8,4),
    limitError       = getBitMap(byte8,3),
    lampArcPowerOn   = getBitMap(byte8,2),
    lampFailure      = getBitMap(byte8,1),
    ballastStatus    = getBitMap(byte8,0)}
    -- each flag returned is a boolean and string value pair
    return stFlgs
end

-- make the group membership string
-- example format: group = '' or '0,3,4,8,13,15'
-- group bit order: 15..8, 7..0
local function getGroupMembership(msb, lsb)

    local DALIGroup = {}
    local bitMask   = 0x01
    for group = 0, 15 do
        if (group == 8) then bitMask = 0x01 end
        if (group <= 7) then  -- do lsb
            if (bitFunctions.band(lsb, bitMask) ~= 0x00) then table.insert(DALIGroup, tostring(group)) end
        else  -- do msb
            if (bitFunctions.band(msb, bitMask) ~= 0x00) then table.insert(DALIGroup, tostring(group)) end
        end
        bitMask = bitFunctions.lshift(bitMask, 1)
    end

    return table.concat(DALIGroup, ',')
end

-- The Initialise command (258) triggers a initialisation period timer. The address commands
-- 259 to 270 are only allowed to be executed while the initialisation period timer is running.
local function addressCmdsNotAllowed(cmdCode)
    if ((not m_TimingInitPeriod) and (cmdCode >= 259) and (cmdCode <= 270)) then
        debug('error: command only allowed during the initialisation sequence')
        return true
    end
    return false
end

-- A configuration command must be repeated within 100 ms, otherwise it is totally ignored.
-- In all cases the slave will not reply with any data. These commands include 32 to 128,
-- DALI_INIT (258) and DALI_RAND (259). ie reset/init/rand, DTR, fade and scene / group commands.
-- Note: the application specific extension commands may also require the msg repeat?
-- These could be flags in the commands array instead of this set up.
--[[
DALI_RESET
DALI_DTR_ACTUAL_LEV
DALI_DTR_MAX_LEV
DALI_DTR_MIN_LEV
DALI_DTR_SYS_FAIL_LEV
DALI_DTR_PWR_ON_LEV
DALI_DTR_FADE_TIME
DALI_DTR_FADE_RATE
DALI_ADD_SCENE_B
DALI_REMOVE_SCENE_B
DALI_ADD_GROUP_B
DALI_REMOVE_GROUP_B
DALI_DTR_S_ADDR
DALI_INIT
DALI_RAND
]]
local function isConfigCommand(cmdCode)
    return (
          ((cmdCode >= 32) and (cmdCode <= 128))
        or (cmdCode == DALI_INIT)
        or (cmdCode == DALI_RAND))
end

-- Most commands make use of a supplied value,
-- which is typically the address but not always.
-- These commands do not use a supplied value.
-- These could be flags in the commands array instead of this set up.
local function cmdValueRequired(cmdCode)
    return not -- required to have an associated value
      (( cmdCode == DALI_LINK_CHECK  )
    or ( cmdCode == DALI_TERMINATE   )
    or ( cmdCode == DALI_RAND        )
    or ( cmdCode == DALI_COMPARE     )
    or ( cmdCode == DALI_WITH_DRAW   )
    or ( cmdCode == DALI_Q_S_ADDR    )
    or ( cmdCode == DALI_PHYS_SEL    ))
end

-- there are 16 Scenes and 16 Groups with commands for each
local function makeSceneGroupCommandAsNeeded(cmd, arcSceneGroupOffset)
    local cmdCode = cmd.commandCode

    if ( not ( -- a scene or group command return
       ( cmdCode == DALI_GO_TO_SCENE    )
    or ( cmdCode == DALI_ADD_SCENE_B    )
    or ( cmdCode == DALI_REMOVE_SCENE_B )
    or ( cmdCode == DALI_ADD_GROUP_B    )
    or ( cmdCode == DALI_REMOVE_GROUP_B )
    or ( cmdCode == DALI_Q_SCENE_LEV_B  ))) then return end

    debug('is a scene or group command with number')
    local offset = tonumber(arcSceneGroupOffset)
    if (offset == nil) then
        debug('error: scene or group is nil: using 0')
        cmd.cmdCodeXXXX = cmdCode
        return
    elseif ((offset < 0) or (offset > 15)) then
        debug('error: scene or group out of range: '..offset..': using 0')
        cmd.cmdCodeXXXX = cmdCode
        return
    end

    cmd.cmdCodeXXXX = cmdCode + offset
    return
end

-- XOR's all the bytes
-- XORing the data and the checksum itself will always equals 0x00
local function getXORchecksum(txMsgTable)
    local checksum = 0
    for _, v in ipairs(txMsgTable) do checksum = bitFunctions.bxor(checksum, v) end
    return checksum
end

-- make TX message CL_DIDIO, TRIDONIC_SCI_1
local function buildTXmsg1(header, msbDALI, lsbDALI)
    local txMsgTable = {header, 0, 0, 0, msbDALI, lsbDALI}
    local checksum   = getXORchecksum(txMsgTable)
    table.insert(txMsgTable, checksum)

--[[  just testing
    debug('Checking: header, msbDALI, lsbDALI, checksum')
    debug(header)
    debug(msbDALI)
    debug(lsbDALI)
    debug(checksum)
    debug(string.format('%s <0x%02X 0x%02X 0x%02X 0x%02X 0x%02X 0x%02X 0x%02X>','buildTXmsg()',header,0,0,0,msbDALI,lsbDALI,checksum))
]]
    return txMsgTable
end

-- make TX message TRIDONIC_SCI_2
local function buildTXmsg2(header, msbDALI, lsbDALI)
    local txMsgTable = {header, 0, msbDALI, lsbDALI}
    local checksum   = getXORchecksum(txMsgTable)
    table.insert(txMsgTable, checksum)
    return txMsgTable
end

-- accommodate different manufacturers if possible
local function setGatewayType(gateway)
    GATEWAY_TYPE = tonumber(gateway)
    local invalidGateway = true
    if (GATEWAY_TYPE == CL_DIDIO) then
        invalidGateway = false
        IP_PORT    = 4000
        LINK_CHK   = 0xC0  -- LINK_CHK  = gateway initialised? No DALI command is sent. Response is: 0x50 = OK
        EXPECT_NR  = 0xA3  -- EXPECT_NR = DALI SCI command results in no a response.    Response is: 0x52 = No
        EXPECT_R   = 0x83  -- EXPECT_R  = DALI SCI command results in a response.       Response is: 0x50, 0x52, 0x53 = data
        buildTXmsg = buildTXmsg1
        RX_MSG_LEN = 3
        DALI_RX_INIT_OK     = 0x50   -- DALI SCI rx header init
        DALI_RX_RESPONSE    = 0x51   -- DALI SCI rx header with response
        DALI_RX_NO_RESPONSE = 0x52   -- DALI SCI rx header with no response
        DALI_RX_ERROR       = 0x53   -- DALI SCI rx header DALI error - comms collision may have occurred
        FIND_RESULT_BYTES   = 0
    elseif (GATEWAY_TYPE == TRIDONIC_SCI_1) then
        -- data transfer mode 1 (DALI SCI)
        invalidGateway = false
        IP_PORT    = 50000
        LINK_CHK   = 0x40
        EXPECT_NR  = 0x20  -- immediate reply to PC; not expecting a DALI response
        EXPECT_R   = 0x00
        buildTXmsg = buildTXmsg1
        RX_MSG_LEN = 3
        DALI_RX_INIT_OK     = 0x50  -- the 5 is the gateway identifier
        DALI_RX_RESPONSE    = 0x51
        DALI_RX_NO_RESPONSE = 0x52
        DALI_RX_ERROR       = 0x53
        FIND_RESULT_BYTES   = 0
    elseif (GATEWAY_TYPE == TRIDONIC_SCI_2) then
        -- data transfer mode 2 (DALI SC2)
        invalidGateway = false
        IP_PORT    = 50000
        LINK_CHK   = 0xC0
        EXPECT_NR  = 0xA3
        EXPECT_R   = 0x83
        buildTXmsg = buildTXmsg2
        RX_MSG_LEN = 5
        DALI_RX_INIT_OK     = 0x60  -- the 6 is the gateway identifier
        DALI_RX_RESPONSE    = 0x62
        DALI_RX_NO_RESPONSE = 0x61
        DALI_RX_ERROR       = 0x67
        FIND_RESULT_BYTES   = 1
    else
        GATEWAY_TYPE = 0
    end
    return invalidGateway
end

-- make the check gateway command message
-- LINK_CHK indicates to just do a link check
-- No DALI bus command occurs
local function buildCheckGatewayCommand()
    -- yikes!! b0 enables or disables the gateway!
    -- b0 must be high for TRIDONIC_SCI_1
    -- DATA_HI = 00h and DATA_LO = 01h, then enable
    -- DATA_HI = 00h and DATA_LO = 00h, then disable (default: enable)
    if (GATEWAY_TYPE == TRIDONIC_SCI_1) then
        return buildTXmsg(LINK_CHK, 0x00, 0x01)
    end

    return buildTXmsg(LINK_CHK, 0x00, 0x00)
end

--[[
The 'S' bit is bit zero of the msb byte
S bit = 0             msb        lsb
Arc command           0AAAAAA0   LLLLLLLL   Arc command: short address: L = level
Arc command           100AAAA0   LLLLLLLL   Arc command: group address: L = level
Reserved ??           101AAAA0   ????????
Reserved ??           110AAAA0   ????????
Reserved ??           111AAAA0   ????????

S bit = 1
Short addresses (64)  0AAAAAA1   CCCCCCCC   Commands:   0 to 255
Group addresses (16)  100AAAA1   CCCCCCCC   Commands:   0 to 255
Special command       101CCCC1   DDDDDDDD   Commands: 256 to 271 =  (0+256 to 15+256) lshift 1 or 0xA0 or S bit
Special command       110CCCC1   DDDDDDDD   Commands: 272 to 287 = (16+256 to 31+256) lshift 1 or 0xC0 or S bit
Broadcast             11111111   CCCCCCCC   Commands:   0 to 255 is broadcast
]]

-- make a Direct Arc command message
-- the S flag is zero: that's an arc command
local function buildArcCommand(arcAddress, arcValue)
    arcAddress = bitFunctions.lshift(arcAddress, 1)
    arcAddress = bitFunctions.band(arcAddress, 0xFF)

    return buildTXmsg(EXPECT_NR, arcAddress, arcValue)
end

-- make a DALI command message
local function buildCommand(command, commandValue)
--[[  just testing
    if (not commandValue) then
        debug('buildCommand() commandValue is nil - replacing with 0x00')
        commandValue = 0x00
    end
]]
    local msbDALI = 0x00
    local lsbDALI = 0x00

    -- default: command does not result in a DALI bus response
    local header = EXPECT_NR

    if ((command >= 0) and (command <= 255)) then
        -- command is in the lsb, address in the msb
        msbDALI = commandValue

        -- S flag is 1: the following txByteLsb will be a DALI command
        -- This will also correctly handle a broadcast address (0x7F)
        local BIT_S_DALI = 0x01
        msbDALI = bitFunctions.bor(bitFunctions.lshift(msbDALI, 1), BIT_S_DALI)
        lsbDALI = command

        -- for some lsb type commands
        -- anything between 0x81 and 0xFF returns a response
        if ((command >= 129) and (command <= 255)) then
            header = EXPECT_R
        end
    elseif ((command >= 256) and (command <= 271)) then
        -- command is in the msb
        -- Special command: 101CCCC1
        msbDALI = bitFunctions.bor(bitFunctions.lshift((command - 256), 1), 0xA1)

        -- some msb commands have an associated value and some don't
        lsbDALI = 0x00
        if (commandValue) then lsbDALI = commandValue end

        -- these three commands (260, 268, 269) result in a response
        if ((command == DALI_COMPARE) or (command == DALI_V_S_ADDR) or (command == DALI_Q_S_ADDR)) then
            header = EXPECT_R
        end
    elseif ((command >= 272) and (command <= 287)) then
        -- command is in the msb
        -- Special command: 110CCCC1
        msbDALI = bitFunctions.bor(bitFunctions.lshift((command - 256 - 16), 1), 0xC1)

        -- some msb commands have an associated value and some don't
        lsbDALI = 0x00
        if (commandValue) then lsbDALI = commandValue end
    else
        debug('buildCommand() command number is bad - replacing with 0')
        commandValue = 0x00
    end

    -- confine to 8 bits after the left shifts above
    msbDALI = bitFunctions.band(msbDALI, 0xFF)

    return buildTXmsg(header, msbDALI, lsbDALI)
end

-- report what was RX'ed in the message buffer
local function rxMsgReport(rxMsgTable, cmdStr, cmdValue)
    local report = {'received hex: '}
    local hex = {}
    for i = 1, RX_MSG_LEN do
        if (rxMsgTable[i]) then
            table.insert(hex, string.format('%02X', rxMsgTable[i]))
        else
            table.insert(hex, 'nil')
        end
    end
    table.insert(report, table.concat(hex, ','))
    table.insert(report, ' in response to ')
    table.insert(report, cmdStr)
    table.insert(report, ' command with command parameter equal to ')
    table.insert(report, tostring(cmdValue))
    debug(table.concat(report))

    if     (FIND_RESULT_BYTES == 0) then return rxMsgTable[1], rxMsgTable[2]
    elseif (FIND_RESULT_BYTES == 1) then return rxMsgTable[1], rxMsgTable[4]
    else return nil, nil end
end

-- using the RAW protocol: this function gets called for every RX'ed byte
local function updateMsgBuffer(RXedMsgChar)
    local bufferFull    = false
    local checksumError = true

    local RXedMsgByte = RXedMsgChar:byte()

    -- fill the RX message buffer
    table.insert(rxMsgTable, RXedMsgByte)

    -- if the RX buffer is full then validate the checksum
    if (#rxMsgTable == RX_MSG_LEN) then
        -- HACK2 rxMsgTable = {0x51, 0xFF, 0xAE}  response with data equal to 0xFF
        bufferFull = true
        local hexString = byteArrayToHexString(rxMsgTable)

        local checksum = getXORchecksum(rxMsgTable)
        checksumError = (checksum ~= 0x00)
        if (checksumError) then
            rxMsgTable = {}
            debug('incoming: buffer is full: '..hexString..' - checksum error detected')
        else
            debug('incoming: buffer is full: '..hexString..' - checksum is OK')
        end
    end

    -- if the RX buffer has overflowed (somehow), then that's a problem
    if (#rxMsgTable > RX_MSG_LEN) then
        bufferFull = true
        debug('incoming: buffer overflowed: '..byteArrayToHexString(rxMsgTable))
        rxMsgTable = {}
    end

    return bufferFull, checksumError
end

-- transmit the command to the DALI bus
local function sendToDALI(txMsgTable)
    -- If we send a message we can always expect a new reply.
    -- So clear the RX msg buffer, given that expectation.
    rxMsgTable = {}
--[[ HACK2 ]]
    if (not luup.io.is_connected(THIS_LUL_DEVICE)) then
        m_TaskHandle = luup.task('No LAN connection to DALI gateway', TASK_ERROR, PLUGIN_NAME, m_TaskHandle)
        debug('no LAN connection to DALI gateway')
        --luup.set_failure(1, THIS_LUL_DEVICE)
        return false
    end

    local txMsg = byteArrayToString(txMsgTable)
    debug('sending hex: '..byteArrayToHexString(txMsgTable))
--[[ HACK2 ]]
    luup.io.intercept(THIS_LUL_DEVICE)
    -- result can be nil, false, or true;  we'll test for true
    local result = luup.io.write(txMsg)
    if (result ~= true) then
        m_TaskHandle = luup.task('Cannot send message - comms error', TASK_ERROR, PLUGIN_NAME, m_TaskHandle)
        debug('Cannot send message - comms error')
        --luup.set_failure(1, THIS_LUL_DEVICE)
        return false
    end

    return true
end

-- do the sending and receiving
local function doTXRXmsg(command, commandValue)

    -- build the command message for this command
    local txMsgTable = command:txFunction(commandValue)

    -- send the command
    local TXRXmsgOk = false
    local statusMsg  = nil

    if (not sendToDALI(txMsgTable)) then
        statusMsg = 'TX error or timeout'
        return TXRXmsgOk, statusMsg
    end

    local RX_TIME_OUT_SECS = 2
    while true do
        -- using raw protocol; should get one only char for each read
        local RXedMsgChar = luup.io.read(RX_TIME_OUT_SECS, THIS_LUL_DEVICE)
        if (not RXedMsgChar) then
            statusMsg = 'RX timeout'
            break
        end

        local bufferFull, checksumError = updateMsgBuffer(RXedMsgChar)
        if (bufferFull) then
            if (checksumError) then
                statusMsg = 'checksum/overflow error detected'
                break
            else
               -- everything went really well
                TXRXmsgOk = true
                statusMsg = 'TX RX all OK'
                break
            end
        end
        -- HACK do we need this on a per char basis?
        -- luup.io.intercept(THIS_LUL_DEVICE)

        -- get next char
    end
    return TXRXmsgOk, statusMsg
end

--------------------------------------------------------------------------------
-- start command table
--------------------------------------------------------------------------------
local DALI_COMMANDS = {

    -- a command, which just checks the link to the DALI gateway
    -- no DALI command is actually sent on the DALI bus
    ["CheckGateway"] = {
    description = "Check if the gateway is currently available.",
    commandCode = DALI_LINK_CHECK,
    txFunction  = function (self, dummy)
        return buildCheckGatewayCommand()
    end
    },

    -- not a DALI command as such: depends on the Arc/DALI flag
    -- "OFF" sets the ballast off (same as power level 0)
    -- "DALI_MASK" stops any fade in progress (same as power level 255)
    ["DirectArcCommand"] = {
    description = "Set light level to the arc value using the actual FADE TIME.",
    commandCode = DALI_DIRECT_ARC,
    arcValue    = DALI_MAX_LEVEL,
    txFunction  = function (self, address)
        return buildArcCommand(address, self.arcValue)
    end
    },

    ["Off"] = {
    description = "Extinguish the lamp immediately without fading.",
    commandCode = DALI_OFF_NF,
    txFunction  = function (self, address)
        return buildCommand(DALI_OFF_NF, address)
    end
    },

    ["Up"] = {
    description = "Dim up for 200 ms (execution time) using the selected 'FADE RATE'",
    commandCode = DALI_UP,
    txFunction  = function (self, address)
        return buildCommand(DALI_UP, address)
    end
    },

    ["Down"] = {
    description = "Dim down for 200 ms (execution time) using the selected 'FADE RATE'.",
    commandCode = DALI_DOWN,
    txFunction  = function (self, address)
        return buildCommand(DALI_DOWN, address)
    end
    },

    ["StepUp"] = {
    description = "Set the actual arc power level one step higher immediately without fading.",
    commandCode = DALI_STEP_UP,
    txFunction  = function (self, address)
        return buildCommand(DALI_STEP_UP, address)
    end
    },

    ["StepDown"] = {
    description = "Set the actual arc power level one step lower immediately without fading.",
    commandCode = DALI_STEP_DOWN,
    txFunction  = function (self, address)
        return buildCommand(DALI_STEP_DOWN, address)
    end
    },

    ["RecallMaxLevel"] = {
    description = "Set the actual arc power level to the 'MAX LEVEL' without fading.",
    commandCode = DALI_R_MAX,
    txFunction  = function (self, address)
    return buildCommand(DALI_R_MAX, address)
    end
    },

    ["RecallMinLevel"] = {
    description = "Set the actual arc power level to the 'MIN LEVEL' without fading.",
    commandCode = DALI_R_MIN,
    txFunction  = function (self, address)
        return buildCommand(DALI_R_MIN, address)
    end
    },

    ["StepDownOff"] = {
    description = "Step down and then turn off.",
    commandCode = DALI_DOWN_OFF,
    txFunction  = function (self, address)
        return buildCommand(DALI_DOWN_OFF, address)
    end
    },

    ["StepUpOn"] = {
    description = "Turn on and step up.",
    commandCode = DALI_ON_UP,
    txFunction  = function (self, address)
        return buildCommand(DALI_ON_UP, address)
    end
    },
    -- in this commands, cmdCodeXXXX is modified to suit the scene number
    ["GoToScene"] = {
    description = "Set the actual arc power level to the value stored for scene XXXX using the actual fade time.",
    commandCode = DALI_GO_TO_SCENE,
    cmdCodeXXXX = 0x00,
    txFunction  = function (self, address)
        return buildCommand(self.cmdCodeXXXX, address)
    end
    },

    ["Reset"] = {
    description = "Reset All Parameters To Default.",
    commandCode = DALI_RESET,
    txFunction  = function (self, address)
        return buildCommand(DALI_RESET, address)
    end
    },

    ["StoreLightLevelInDTR"] = {
    description = "Store actual arc power level in the DTR without changing the current light intensity.",
    commandCode = DALI_DTR_ACTUAL_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_ACTUAL_LEV, address)
    end
    },

    ["DTRAsMaxLevel"] = {
    description = "Save the value in Data Transfer Register as new 'MAX LEVEL'.",
    commandCode = DALI_DTR_MAX_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_MAX_LEV, address)
    end
    },

    ["DTRAsMinLevel"] = {
    description = "Save the value in Data Transfer Register as new 'MIN LEVEL'.",
    commandCode = DALI_DTR_MIN_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_MIN_LEV, address)
    end
    },

    ["DTRAsFailureLevel"] = {
    description = "Save the value in Data Transfer Register as new 'SYSTEM FAILURE LEVEL'.",
    commandCode = DALI_DTR_SYS_FAIL_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_SYS_FAIL_LEV, address)
    end
    },

    ["DTRAsPowerOnLevel"] = {
    description = "Save the value in Data Transfer Register as new 'POWER ON LEVEL'.",
    commandCode = DALI_DTR_PWR_ON_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_PWR_ON_LEV, address)
    end
    },

    ["StoreDTRAsFadeTime"] = {
    description = "Set the 'FADE TIME'.",
    commandCode = DALI_DTR_FADE_TIME,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_FADE_TIME, address)
    end
    },

    ["StoreDTRAsFadeRate"] = {
    description = "Store DTR as 'FADE RATE'.",
    commandCode = DALI_DTR_FADE_RATE,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_FADE_RATE, address)
    end
    },
    -- in the next four commands, cmdCodeXXXX is modified to suit the scene or group number
    ["StoreDTRAsScene"] = {
    description = "Save the value in Data Transfer Register as a new level of the scene XXXX.",
    commandCode = DALI_ADD_SCENE_B,
    cmdCodeXXXX = 0x00,
    txFunction  = function (self, address)
        -- this adds a device to a particular scene, as a side effect of
        -- setting the level for the device in that particular scene
        -- Setting the level to DALI_MASK removes the device from the scene
        return buildCommand(self.cmdCodeXXXX, address)
    end
    },

    ["RemoveFromScene"] = {
    description = "Remove the ballast from scene XXXX.",
    commandCode = DALI_REMOVE_SCENE_B,
    cmdCodeXXXX = 0x00,
    txFunction  = function (self, address)
        return buildCommand(self.cmdCodeXXXX, address)
    end
    },

    ["AddToGroup"] = {
    description = "Add the ballast to group XXXX.",
    commandCode = DALI_ADD_GROUP_B,
    cmdCodeXXXX = 0x00,
    txFunction  = function (self, address)
        return buildCommand(self.cmdCodeXXXX, address)
    end
    },

    ["RemoveFromGroup"] = {
    description = "Remove the ballast from group XXXX.",
    commandCode = DALI_REMOVE_GROUP_B,
    cmdCodeXXXX = 0x00,
    txFunction  = function (self, address)
        return buildCommand(self.cmdCodeXXXX, address)
    end
    },

    -- set Short Address to value in DTR: 0AAA AAA1 or 1111 1111 (DALI_MASK)
    ["StoreDTRAsShortAddress"] = {
    description = "Save the value in the DTR as new short address.",
    commandCode = DALI_DTR_S_ADDR,
    txFunction  = function (self, address)
        return buildCommand(DALI_DTR_S_ADDR, address)
    end
    },

-- none of the above get a response containing data in the actual reply
--------------------------------------------------------------------------------

    ["QueryStatus"] = {
    description = "Query device status.",
    commandCode = DALI_Q_STATUS,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_STATUS, address)
    end,

    rxFunction = function (self, byte1, status)
        if (byte1 == DALI_RX_RESPONSE) then
            return status
        else
            return nil
        end
    end
    },

    ["QueryBallast"] = {
    description = "Ask if there is a ballast with the given address that is able to communicate.",
    commandCode = DALI_Q_BALLAST,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_BALLAST, address)
    end,

    rxFunction = function (self, byte1, status)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryLampFailure"] = {
    description = "Ask if there is a lamp problem at the given address.",
    commandCode = DALI_Q_LAMP_FAILURE,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_LAMP_FAILURE, address)
    end,

    rxFunction = function (self, byte1, byte2)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryLampPowerOn"] = {
    description = "Ask if there is a lamp operating at the given address.",
    commandCode = DALI_Q_LAMP_POWER_ON,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_LAMP_POWER_ON, address)
    end,

    rxFunction = function (self, byte1, byte2)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryLimitError"] = {
    description = "Ask if the last requested arc power level at the given address could not be met.",
    commandCode = DALI_Q_LIMIT_ERROR,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_LIMIT_ERROR, address)
    end,

    rxFunction = function (self, byte1, byte2)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryResetState"] = {
    description = "Ask if the ballast is in 'RESET STATE'.",
    commandCode = DALI_Q_RESET_STATE,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_RESET_STATE, address)
    end,

    rxFunction = function (self, byte1, byte2)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryMissingShortAddress"] = {
    description = "Ask if the ballast Missing Short Address.",
    commandCode = DALI_Q_MISSING_SHORT,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_MISSING_SHORT, address)
    end,

    rxFunction = function (self, byte1, byte2)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryVersion"] = {
    description = "Ask for the version number of the IEC standard document met by the software and the hardware of the present ballast.",
    commandCode = DALI_Q_VER_NUM,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_VER_NUM, address)
    end,

    rxFunction = function (self, byte1, version)
        if (byte1 == DALI_RX_RESPONSE) then
            return version
        else
            return nil
        end
    end
    },

    ["QueryDTR"] = {
    description = "Returns contents of DTR as 8 bit number.",
    commandCode = DALI_Q_DTR_CONTENTS,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_DTR_CONTENTS, address)
    end,

    rxFunction = function (self, byte1, dtr)
        if (byte1 == DALI_RX_RESPONSE) then
            return dtr
        else
            return nil
        end
    end
    },

    ["QueryDeviceType"] = {
    description = "Query Device Type.",
    commandCode = DALI_Q_TYPE,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_TYPE, address)
    end,

    rxFunction = function (self, byte1, deviceType)
        if (byte1 == DALI_RX_RESPONSE) then
            return deviceType
        else
            return nil
        end
    end
    },

    ["QueryPhysicalMinLevel"] = {
    description = "Query physical minimum level.",
    commandCode = DALI_Q_PHYS_MIN_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_PHYS_MIN_LEV, address)
    end,

    rxFunction = function (self, byte1, minLevel)
        if (byte1 == DALI_RX_RESPONSE) then
            return minLevel
        else
            return nil
        end
    end
    },

    ["QueryPowerFailure"] = {
    description = "Query power failure.",
    commandCode = DALI_Q_POWER_FAILURE,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_POWER_FAILURE, address)
    end,

    rxFunction = function (self, byte1, byte2)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryDTR1"] = {
    description = "Returns contents of DTR1 as 8 bit number.",
    commandCode = DALI_Q_DTR1_CONTENTS,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_DTR1_CONTENTS, address)
    end,

    rxFunction = function (self, byte1, dtr)
        if (byte1 == DALI_RX_RESPONSE) then
            return dtr
        else
            return nil
        end
    end
    },

    ["QueryDTR2"] = {
    description = "Returns contents of DTR2 as 8 bit number.",
    commandCode = DALI_Q_DTR2_CONTENTS,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_DTR2_CONTENTS, address)
    end,

    rxFunction = function (self, byte1, dtr)
        if (byte1 == DALI_RX_RESPONSE) then
            return dtr
        else
            return nil
        end
    end
    },

    ["QueryActualLevel"] = {
    description = "Query Actual Lamp Level.",
    commandCode = DALI_Q_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_LEV, address)
    end,

    rxFunction = function (self, byte1, actLevel)
        if (byte1 == DALI_RX_RESPONSE) then
            return actLevel
        else
            return nil
        end
    end
    },

    ["QueryMaxLevel"] = {
    description = "Query Maximum Lamp Level.",
    commandCode = DALI_Q_MAX,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_MAX, address)
    end,

    rxFunction = function (self, byte1, maxLevel)
        if (byte1 == DALI_RX_RESPONSE) then
            return maxLevel
        else
            return nil
        end
    end
    },

    ["QueryMinLevel"] = {
    description = "Query Minimum Lamp Level.",
    commandCode = DALI_Q_MIN,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_MIN, address)
    end,

    rxFunction = function (self, byte1, minLevel)
        if (byte1 == DALI_RX_RESPONSE) then
            return minLevel
        else
            return nil
        end
    end
    },

    ["QueryPowerOnLevel"] = {
    description = "Query power on level.",
    commandCode = DALI_Q_PWR_ON_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_PWR_ON_LEV, address)
    end,

    rxFunction = function (self, byte1, onLevel)
        if (byte1 == DALI_RX_RESPONSE) then
            return onLevel
        else
            return nil
        end
    end
    },

    ["QueryFailureLevel"] = {
    description = "Query system failure Level.",
    commandCode = DALI_Q_SYS_FAIL_LEV,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_SYS_FAIL_LEV, address)
    end,

    rxFunction = function (self, byte1, failLevel)
        if (byte1 == DALI_RX_RESPONSE) then
            return failLevel
        else
            return false
        end
    end
    },

    ["QueryFadeTimeRate"] = {
    description = "Query Fade Time/Fade Rate.",
    commandCode = DALI_Q_FADE,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_FADE, address)
    end,

    rxFunction = function (self, byte1, byte2)
        if (byte1 == DALI_RX_RESPONSE) then
            -- msb nibble is time; lsb is rate
            return {fadeRate = bitFunctions.band(byte2, 0x0F),
                    fadeTime = bitFunctions.rshift(byte2, 4)}
        else
            return nil
        end
    end
    },

    ["QuerySceneLevel"] = {
    description = "Query the scene level.",
    commandCode = DALI_Q_SCENE_LEV_B,
    cmdCodeXXXX = 0x00,
    txFunction  = function (self, address)
        return buildCommand(self.cmdCodeXXXX, address)
    end,

    rxFunction = function (self, byte1, sceneLevel)
        if (byte1 == DALI_RX_RESPONSE) then
            return sceneLevel
        else
            return nil
        end
    end
    },

    ["QueryGroupL"] = {
    description = "Query Group - low.",
    commandCode = DALI_Q_R_GRP_L,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_R_GRP_L, address)
    end,

    rxFunction = function (self, byte1, grpL)
        if (byte1 == DALI_RX_RESPONSE) then
            return grpL
        else
            return nil
        end
    end
    },

    ["QueryGroupH"] = {
    description = "Query Group - high.",
    commandCode = DALI_Q_R_GRP_H,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_R_GRP_H, address)
    end,

    rxFunction = function (self, byte1, grpH)
        if (byte1 == DALI_RX_RESPONSE) then
            return grpH
        else
            return nil
        end
    end
    },

    ["QueryRandomAddressH"] = {
    description = "Query Random Address - high.",
    commandCode = DALI_Q_R_ADDR_H,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_R_ADDR_H, address)
    end,

    rxFunction = function (self, byte1, rndAddrH)
        if (byte1 == DALI_RX_RESPONSE) then
            return rndAddrH
        else
            return nil
        end
    end
    },

    ["QueryRandomAddressM"] = {
    description = "Query Random Address - middle.",
    commandCode = DALI_Q_R_ADDR_M,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_R_ADDR_M, address)
    end,

    rxFunction = function (self, byte1, rndAddrM)
        if (byte1 == DALI_RX_RESPONSE) then
            return rndAddrM
        else
            return nil
        end
    end
    },

    ["QueryRandomAddressL"] = {
    description = "Query Random Address - low.",
    commandCode = DALI_Q_R_ADDR_L,
    txFunction  = function (self, address)
        return buildCommand(DALI_Q_R_ADDR_L, address)
    end,

    rxFunction = function (self, byte1, rndAddrL)
        if (byte1 == DALI_RX_RESPONSE) then
            return rndAddrL
        else
            return nil
        end
    end
    },

    ["T6QueryFeatures"] = {
    description = "T6 Query features.",
    commandCode = DALI_6_Q_FEATURES,
    txFunction  = function (self, address)
        return buildCommand(DALI_6_Q_FEATURES, address)
    end,

    rxFunction = function (self, byte1, features)
        if (byte1 == DALI_RX_RESPONSE) then
            return features
        else
            return nil
        end
    end
    },

    ["T6QueryFailureStatus"] = {
    description = "T6 Query failure status.",
    commandCode = DALI_6_Q_FAIL_STATUS,
    txFunction  = function (self, address)
        return buildCommand(DALI_6_Q_FAIL_STATUS, address)
    end,

    rxFunction = function (self, byte1, status)
        if (byte1 == DALI_RX_RESPONSE) then
            return status
        else
            return nil
        end
    end
    },

--------------------------------------------------------------------------------
-- Special commands: command is coded into the MSB
-- These commands are processed by all the slaves:
--------------------------------------------------------------------------------
    ["Terminate"] = {
    description = "DALI Terminate.",
    commandCode = DALI_TERMINATE,
    txFunction  = function (self, dummy)
        -- terminate the timer started by the "Initialise" command
        m_TimingInitPeriod = false
        return buildCommand(DALI_TERMINATE)
    end
    },

    ["StoreValueDTR"] = {
    description = "Store 8 bit value XXXX XXXX to DTR.",
    commandCode = DALI_SET_DTR,
    txFunction  = function  (self, dtrValue)
        return buildCommand(DALI_SET_DTR, dtrValue)
    end
    },

    ["Initialise"] = {
    description = "DALI Initialise.",
    commandCode = DALI_INIT,
    txFunction  = function (self, programTheseDevices)
        return buildCommand(DALI_INIT, programTheseDevices)
    end,
    rxFunction = function (self, byte1, byte2)
        m_TimingInitPeriod = true

        -- interval timer, 10 minutes, day = ignore, data = none
        luup.call_timer('m_timerTimeoutInitPeriod', 10, '1m', '', '')

        return true
    end
    },

    ["Randomise"] = {
    description = "DALI Randomise.",
    commandCode = DALI_RAND,
    txFunction  = function (self, dummy)
        return buildCommand(DALI_RAND)
    end
    },

    ["Compare"] = {
    description = "DALI Compare.",
    commandCode = DALI_COMPARE,
    txFunction  = function (self, dummy)
        return buildCommand(DALI_COMPARE)
    end,
    rxFunction = function (self, byte1, byte2)
        if (byte1 ~= DALI_RX_RESPONSE) then return false end
        -- During compare, many devices may respond: Their responses are the same
        -- and they are wire or'ed together, so there are no collisions. Regardless
        -- timing problems can result in the returned value of 0xFF becoming
        -- corrupted. So a DALI_RX_RESPONSE is also considered a yes.
        if (byte2 ~= DALI_YES) then
            debug("this device does not meet spec or bus timing problems: byte2 = "..tonumber(byte2))
        end
        return true -- since DALI_RX_RESPONSE is true
     end
    },

    ["Withdraw"] = {
    description = "DALI Withdraw.",
    commandCode = DALI_WITH_DRAW,
    txFunction  = function (self, dummy)
        return buildCommand(DALI_WITH_DRAW)
    end
    },

    ["SearchHighAddress"] = {
    description = "DALI Search High Address.",
    commandCode = DALI_S_ADRR_H,
    txFunction  = function (self, highAddress)
        return buildCommand(DALI_S_ADRR_H, highAddress)
    end
    },

    ["SearchMiddleAddress"] = {
    description = "DALI Search Middle Address.",
    commandCode = DALI_S_ADRR_M,
    txFunction  = function (self, middleAddress)
        return buildCommand(DALI_S_ADRR_M, middleAddress)
    end
    },

    ["SearchLowAddress"] = {
    description = "DALI Search Low Address.",
    commandCode = DALI_S_ADRR_L,
    txFunction  = function (self, lowAddress)
        return buildCommand(DALI_S_ADRR_L, lowAddress)
    end
    },

    ["ProgramShortAddress"] = {
    description = "DALI Program Short Address.",
    commandCode = DALI_P_S_ADDR,
    txFunction  = function (self, shortAddress)
        return buildCommand(DALI_P_S_ADDR, shortAddress)
    end
    },

    ["VerifyShortAddress"] = {
    description = "DALI Verify Short Address.",
    commandCode = DALI_V_S_ADDR,
    txFunction  = function (self, shortAddress)
        return buildCommand(DALI_V_S_ADDR, shortAddress)
    end,
    rxFunction = function (self, byte1, byte2)
        return (byte1 == DALI_RX_RESPONSE) and (byte2 == DALI_YES)
    end
    },

    ["QueryShortAddress"] = {
    description = "DALI Query Short Address.",
    commandCode = DALI_Q_S_ADDR,
    txFunction  = function (self, dummy)
        return buildCommand(DALI_Q_S_ADDR)
    end,

    rxFunction = function (self, byte1, shortAddr)
        if (byte1 == DALI_RX_RESPONSE) then
            return shortAddr
        else
            return nil
        end
    end
    },

    ["PhysicalSelection"] = {
    description = "DALI Physical Selection.",
    commandCode = DALI_PHYS_SEL,
    txFunction  = function (self, dummy)
        return buildCommand(DALI_PHYS_SEL)
    end
    },

    ["EnableTypeX"] = {
    description = "DALI Enable device type X.",
    commandCode = DALI_EN_DEV_TYPE_X,
    txFunction  = function (self, deviceTypeX)
        return buildCommand(DALI_EN_DEV_TYPE_X, deviceTypeX)
    end
    },

    ["StoreValueDTR1"] = {
    description = "Store 8 bit value XXXX XXXX to DTR1.",
    commandCode = DALI_SET_DTR1,
    txFunction  = function  (self, dtrValue)
        return buildCommand(DALI_SET_DTR1, dtrValue)
    end
    },

    ["StoreValueDTR2"] = {
    description = "Store 8 bit value XXXX XXXX to DTR2.",
    commandCode = DALI_SET_DTR2,
    txFunction  = function  (self, dtrValue)
        return buildCommand(DALI_SET_DTR2, dtrValue)
    end
    }
}
--------------------------------------------------------------------------------
-- end command table
--------------------------------------------------------------------------------

-- validate the command and return it
local function getCommand(cmdStr)
    local cmd = DALI_COMMANDS[cmdStr]
    if (cmdStr == nil) then return false, 'the command string is nil' end
    if (cmd == nil) then return false, ('the command is not in the command array: '..cmdStr) end

    local badCmd = false
    if (not cmd.description) then debug('getCommand(): command missing description')       badCmd = true end
    if (not cmd.commandCode) then debug('getCommand(): missing commandCode')               badCmd = true end
    if (type(cmd.txFunction) ~= 'function') then debug('getCommand(): invalid txFunction') badCmd = true end

    if (badCmd) then
        return false, 'the command array is broken'
    else
        return true, cmd
    end
end

-- This function returns two results and a 3rd if DALI_RX_ERROR is true:
-- The first result is always the boolean OK flag.
-- The second result contains valid data or an error message string
-- The third contains DALI_RX_ERROR for the 'Compare' command
local function executeSingleDALIcommand(cmdStr, cmdValue, arcSceneGroupOffset)

    local ok, cmd = getCommand(cmdStr)
    if (not ok) then return false, cmd end

    debug('') -- make a spacer
    debug('attempting command: \''..cmd.description..'\'')

    -- the address commands (259 to 270) are not allowed during normal operation
    if (addressCmdsNotAllowed(cmd.commandCode)) then
        return false, 'address commands are only allowed while assigning short addresses'
    end

    -- most commands have an associated command value but not all
    if (cmdValueRequired(cmd.commandCode)) then
        debug('cmdValue is required')
        cmdValue = tonumber(cmdValue)
        if (cmdValue == nil) then
            return false, 'required cmdValue is not a number'
        end
    else
        cmdValue = nil
    end

    -- Arc command?
    if (cmd.commandCode == DALI_DIRECT_ARC) then cmd.arcValue = arcSceneGroupOffset end

    -- build all of the command codes for the scenes and groups as needed
    makeSceneGroupCommandAsNeeded(cmd, arcSceneGroupOffset)

    m_LastWasConfigCommand = isConfigCommand(cmd.commandCode)
    if (m_LastWasConfigCommand) then
        debug ('starting DALI CONFIGURATION command: '..cmdStr)
    else
        debug('starting DALI command: '..cmdStr)
    end

    -- final check of cmd; cmdValue can be nil
    if (cmd == nil) then debug('error: cmd is nil') end

--------------------------------------------------------------------------------
    local TXRXmsgOk, statusMsg = doTXRXmsg(cmd, cmdValue)
    -- note that gateways reset their own comms after 100 msec
    luup.sleep(5)  -- give the gateway a short break
--------------------------------------------------------------------------------

    if (not TXRXmsgOk) then return false, statusMsg end

    local byte1, byte2 = rxMsgReport(rxMsgTable, cmdStr, cmdValue)

    -- collisions on the DALI bus are to be expected and need to be accommodated
    -- note that DALI_RX_ERROR is returned
    if (byte1 == DALI_RX_ERROR) then
        return false, 'Comms collision on DALI bus probably occured', DALI_RX_ERROR
    end

    if (byte1 == DALI_RX_INIT_OK) then return true, 'DALI_RX_INIT_OK' end

    if ((byte1 == DALI_RX_RESPONSE) or (byte1 == DALI_RX_NO_RESPONSE)) then
        local result = nil

        -- each command result is handled differently. Dial up the appropriate RX function to act as needed.
        if (cmd.rxFunction) then
            if (type(cmd.rxFunction) ~= 'function') then return false, 'invalid rxFunction' end
            result = cmd:rxFunction (byte1, byte2)
        end

        if (byte1 == DALI_RX_RESPONSE) then
            debug('DALI_RX_RESPONSE was received')
        else
            debug('DALI_RX_NO_RESPONSE was received')
        end
        debug('the RX\'ed data is as follows (numbers are decimal):')
        debug(result)  -- do not concatenate with string above; result var can be nil

        return true, result
    end

    -- some unknown reply
    return false, 'something not good happened'
end

-- This function returns two results and a 3rd if DALI_RX_ERROR is true:
-- The first result is always the boolean OK flag.
-- The second result contains valid data or an error message string, if not ok
-- The third contains DALI_RX_ERROR for the 'Compare' command
-- Trap debug info here. The error msg string is in result.
local function executeDALIcommand(cmdStr, cmdValue, arcSceneGroupOffset)

    local ok, result, daliRxError = executeSingleDALIcommand(cmdStr, cmdValue, arcSceneGroupOffset)
    if (not ok) then
        if (result) then
            debug('executeSingleDALIcommand() failed: '..result,2)
        else
            debug('executeSingleDALIcommand() failed: error msg is nil',2)
        end
        return ok, result, daliRxError
    end

    -- config commands MUST be repeated within 100 msec, otherwise they are ignored
    if (m_LastWasConfigCommand) then
       debug('REPEATING config command - this needs to be done for all config commands')
       ok, result, daliRxError = executeSingleDALIcommand(cmdStr, cmdValue, arcSceneGroupOffset)
       if (not ok) then
            if (result) then
                debug('executeSingleDALIcommand() REPEAT failed: '..result,2)
            else
                debug('executeSingleDALIcommand() REPEAT failed: error msg is nil',2)
            end
            return ok, result, daliRxError
        end
    end

    return ok, result, daliRxError -- return most recent status/result/error
end

-- iterator that returns the IDs of all the DALI lights
local function daliLights()
    local daliLightList = {}

    for deviceID, v in pairs(luup.devices) do
        if ((v.device_num_parent == THIS_LUL_DEVICE)
        and (tostring(v.device_type) == DIMMABLE_LIGHT_DEV)
        and (not v.id:find('Group'))) then
            table.insert(daliLightList, deviceID)
        end
    end

    local i = 0
    local iter = function ()
        i = i + 1
        if daliLightList[i] == nil then return nil
        else return daliLightList[i] end
    end

    return iter
end

-- default the Wattage to xyz Watts for all child devices
local function setPowerConsumption(Watts)
    local currentValue = nil

    for light in daliLights() do
        currentValue = luup.variable_get(ENERGY_METERING_SID, 'UserSuppliedWattage', light)
        if (currentValue == nil) then
		    -- Create the UserSuppliedWattage variable:
			-- This var is used as the source value when the light's power consumption
			-- calculations are in action. The result is written to the Watts variable.
            luup.variable_set(ENERGY_METERING_SID, 'UserSuppliedWattage', tostring(Watts), light)
        end
    end
end

local function updateDeviceStatus(targetValue, updateWatts, lul_device)
	local onOff = '1'
    targetValue = tonumber(targetValue)
    if (targetValue == 0) then onOff = '0' end

    updateVariable('Status', onOff, SWP_SID, lul_device)
    updateVariable('LoadLevelTarget', tostring(targetValue), SWD_SID, lul_device) -- needed for AltUI
    updateVariable('LoadLevelStatus', tostring(targetValue), SWD_SID, lul_device)

    -- only needs to be done for single lights, not for groups
    if (updateWatts) then
        -- use the dimmer setting and UserSuppliedWattage to calculate the 'Watts' var
        local usWatts = tonumber(luup.variable_get(ENERGY_METERING_SID, 'UserSuppliedWattage', lul_device) or '0')
        updateVariable('Watts', tostring(usWatts*(targetValue/100.0)), ENERGY_METERING_SID, lul_device)
	end
end

local function doQueryGroup(DALIaddress)
    local okH, groupH = executeDALIcommand('QueryGroupH', DALIaddress)
    local okL, groupL = executeDALIcommand('QueryGroupL', DALIaddress)

    -- build the group membership; example format: group = '0,3,4,8,13,15'
    if (okH and okL and groupH and groupL) then
        local membership = getGroupMembership(groupH, groupL)
        return true, membership
    else
        return false, 'doQueryGroup() failed'
    end
end

-- if the short address is missing or duplicated over multiple devices
-- then knowing the random address is useful
local function doQueryRandomAddress(DALIaddress)
    local okH, addressH = executeDALIcommand('QueryRandomAddressH', DALIaddress)
    local okM, addressM = executeDALIcommand('QueryRandomAddressM', DALIaddress)
    local okL, addressL = executeDALIcommand('QueryRandomAddressL', DALIaddress)

    if (okH and okM and okL and addressH and addressM and addressL) then
        return true, (addressH * 65536) + (addressM * 256) + addressL
    else
        return false, 'doQueryRandomAddress() failed'
    end
end

-- transfer a value to its destination via the DTR
function transferViaDTR(transferValue, toAddress, saveDTRas, arcSceneGroupOffsetStr)
    transferValue = tonumber(transferValue)
    toAddress     = tonumber(toAddress)
    local arcSceneGroupOffset = tonumber(arcSceneGroupOffsetStr) or 0

    -- store the transferValue ---> DTR ---> saveDTRas in the DALIaddress
    local ok1 = executeDALIcommand('StoreValueDTR', transferValue)
    local ok2 = executeDALIcommand(saveDTRas, toAddress, arcSceneGroupOffset)
    return ok1 and ok2
end

-- set the search registers
local function setSearchAddress (searchAddress, lastH, lastM, lastL)
    -- split the searchAddress into three bytes
    local addrH   = math.floor(searchAddress/65536)
    local amountH = addrH * 65536
    local addrM   = math.floor((searchAddress-amountH)/256)
    local amountM = addrM * 256
    local addrL   = searchAddress - amountH - amountM

    -- sanity check to make sure this worked
    if (searchAddress ~= (amountH + amountM + addrL)) then
        debug('setSearcaddrH(): setSearchAddress split failed')
        return false, lastH, lastM, lastL
    end

    -- set the search registers in all the devices. Only update the registers that need changing.
    local okH = true
    local okM = true
    local okL = true
    if (lastH ~= addrH) then okH = executeDALIcommand('SearchHighAddress',   addrH) end
    if (lastM ~= addrM) then okM = executeDALIcommand('SearchMiddleAddress', addrM) end
    if (lastL ~= addrL) then okL = executeDALIcommand('SearchLowAddress',    addrL) end

    if (not (okH and okM and okL)) then
        debug('setSearchAddress(): failed to set search registers')
        return false, lastH, lastM, lastL
    end

    return true, addrH, addrM, addrL
end

 -- go through the search addresses looking for a match
function searchForDevices()
    -- HACK2 test code: used to fake a search
    -- HACK2 local deviceRandomAddress = 8000001

    local doneAllDevices = true
    local ok             = false
    local high           = 16777215  -- 2^24-1
    local searchAddress  = 0
    local low            = 0
    local lastH          = -1
    local lastM          = -1
    local lastL          = -1

    -- perform the binary search for the DALI devices
    repeat
        searchAddress = math.floor((low+high)/2)

        ok, lastH, lastM, lastL = setSearchAddress(searchAddress, lastH, lastM, lastL)
        if (not ok) then debug('searchForDevices(): could not set search address') return ok, nil end

        -- if a DALI bus collision occurs, which is possible here, then loop around again and have another go
        local done          = false
        local okCompare     = false
        local replyWasYes   = false
        local daliRxError   = 0x00
        local retries       = 0
        local MAX_RETRY_CNT = 10
        repeat
            -- we've loaded our search address into the search registers for all of the devices. Now command
            -- all of the devices to each compare its own internal random address with our search address.
            okCompare, replyWasYes, daliRxError = executeDALIcommand('Compare')

             -- if (deviceRandomAddress <= searchAddress) the answer is 'Yes' from potentially multiple devices
            -- At this point DALI_RX_ERROR may be set due to collisions amongst the replying devices
            -- if (deviceRandomAddress > searchAddress) the answer is 'No'
            -- Keep dividing the searchAddress till 24 tests have been performed
            if (okCompare) then
                debug('only one device is replying or none are replying',50)
                done = true
            elseif (daliRxError == DALI_RX_ERROR) then
                debug('multiple devices are replying',50)
                replyWasYes = true
                done        = true
            else  -- some unknown error - do retries
                retries = retries +1
                if (retries >= MAX_RETRY_CNT) then
                    debug('searchForDevices(): max retries exceeded')
                    return false, nil
                end
            end
        until (done)

        -- HACK2 test code: used to fake a search
        -- HACK2 replyWasYes = (deviceRandomAddress <= searchAddress)

        -- if we get a yes reply there are still devices responding
        if (replyWasYes) then doneAllDevices = false end

        debug('searchForDevices(): low -->'..tostring(low)..','..tostring(high)..'<-- high',50)
        -- HACK2 debug('searchForDevices(): deviceRandomAddress -->'..tostring(deviceRandomAddress)..','..tostring(searchAddress)..'<-- searchAddress')

        -- have we arrived at the very last test?
        if (high == low) then
            -- all tests done and never got a yes reply?
            -- then we're done, else someone is out there
            if (doneAllDevices) then
                debug('search complete: no more devices',50)
                return true, doneAllDevices
            end
            --    deviceRandomAddress = searchAddress
            -- or deviceRandomAddress = searchAddress + 1
            local result = 0
            if (replyWasYes) then
                -- yes answer: (deviceRandomAddress = searchAddress)
                result = searchAddress
                debug('Match in YES: deviceRandomAddress is '..result,50)
            else -- but we have had a reply previously - we know you are out there
                -- no answer: (deviceRandomAddress > searchAddress)
                -- deviceRandomAddress can only be greater than searchAddress by one
                -- go back a little
                ok = setSearchAddress(searchAddress +1, lastH, lastM, lastL)
                result = searchAddress +1
                debug('Match in NO: deviceRandomAddress is '..result,50)
            end
        end

        -- we filtered out the equals case above. So it's either less than or greater than at this point
        if (replyWasYes) then
            high = searchAddress - 1  -- yes answer: (deviceRandomAddress <= searchAddress)
        else
            low  = searchAddress + 1  -- no answer: (deviceRandomAddress > searchAddress)
        end

    until (high < low)

    debug('search complete: found a device',50)
    return true, doneAllDevices
end

-- map Vera device to DALI device. An inadvertent setup command can be rectified
-- with a bit of remapping. This is all just in case the DALI addresses change.
-- Note this can be improved upon and should be considered temporary. However
-- any use of DALIaddress should go through this function to allow remapping.
local function getDALIaddress(lul_device)
    local addressMap = {
 [0]=0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    -- let this slip through as is
    [DALI_BROADCAST] = DALI_BROADCAST
    }

    local veraAddress = tonumber(luup.devices[lul_device].id)  -- altid value
    if (veraAddress == nil) then debug('getDALIaddress(): veraAddress is nil') end

    local DALIaddress = addressMap[veraAddress]
    if (not DALIaddress) then debug('getDALIaddress() supplied with invalid DALI address') end
    return DALIaddress
end

-- change fading: see luaStartUp()
-- fadeTime is the time to dim up or down from level a to level b
-- fadeTime = 2^((n/2)-1)    n = 0 to 15
-- fadeRate = 253/fadeTime
--
-- fadeTime is used by the commands: DirectArcCommand and DALI_GO_TO_SCENE
-- fadeRate is used by the commands: DALI_UP and DALI_DOWN
local function fadeChange(lul_device, newFadeTime, newFadeRate)
    local ok = true
    local DALIaddress = getDALIaddress(lul_device)

    -- fade time in seconds = 0.5*(2^n)^0.5  or  2^((n/2)-1)   where n = 0 to 15; (0.5 to 90.5 secs)
    local fadeTimeSecs = 0.5 * (2^newFadeTime)^0.5
    debug('fade time in seconds: '..string.format('%.1f', fadeTimeSecs))

    local ok1 = transferViaDTR(newFadeTime, DALIaddress, 'StoreDTRAsFadeTime')
    ok = ok and ok1

    if (newFadeRate == 0) then
        debug('fadeChange(): error at address:'..DALIaddress..' A new fade rate of zero is not allowed')
        return false
    end

    -- fade rate in steps per second = 506/(2^n)^0.5   where n = 1 to 254; (357.8 to 2.8 steps/secs)
    local stepsPerSec = 506/(2^newFadeRate)^0.5
    debug('steps per second: '..string.format('%.1f', stepsPerSec))

    local ok2 = transferViaDTR(newFadeRate, DALIaddress, 'StoreDTRAsFadeRate')
    ok = ok and ok2

    return ok
end

-- provides a simple json report for a DALI device
local function getDeviceInfo(lcParameters)

    local deviceTypes = {
    'fluorescent lamp',
    'emergency lighting',
    'HID lamp',
    'low voltage halogen lamp',
    'incandescent lamp dimmer',
    'dc-controlled dimmer',
    'LED lamp',                  -- spec part 207
    'switching function',
    'colour control',            -- spec part 209
    'sequencer',
    'optical control',
    [255]='multi device type'}

    local intro = '{"ballastInfo": "'
    local deviceStatusTab = {}

    local DALIaddressStr = lcParameters.daliaddress
    if (not DALIaddressStr) then return intro..'Please enter a valid DALI address"}', 'application/json' end

    local DALIaddress = tonumber(DALIaddressStr)
    if (not DALIaddress) then return intro..'Please enter a valid DALI address"}', 'application/json' end

    debug('Querying device at address: '..DALIaddressStr)
    local ok, membership = doQueryGroup(DALIaddress)

    if (ok and membership) then
        local  ok1, lampPowerOn      = executeDALIcommand('QueryLampPowerOn',        DALIaddress)
        local  ok2, maxLevel         = executeDALIcommand('QueryMaxLevel',           DALIaddress)
        local  ok3, actualLevel      = executeDALIcommand('QueryActualLevel',        DALIaddress)
        local  ok4, minLevel         = executeDALIcommand('QueryMinLevel',           DALIaddress)
        local  ok5, minPhysLevel     = executeDALIcommand('QueryPhysicalMinLevel',   DALIaddress)
        local  ok6, powerOnLevel     = executeDALIcommand('QueryPowerOnLevel',       DALIaddress)
        local  ok7, failureLevel     = executeDALIcommand('QueryFailureLevel',       DALIaddress)
        local  ok8, current          = executeDALIcommand('QueryFadeTimeRate',       DALIaddress)
        local  ok9, version          = executeDALIcommand('QueryVersion',            DALIaddress)
        local ok10, DTRcontents      = executeDALIcommand('QueryDTR',                DALIaddress)
        local ok11, missingShortAddr = executeDALIcommand('QueryMissingShortAddress',DALIaddress)
        local ok12, randomAddress    = doQueryRandomAddress(DALIaddress)
        local ok13, deviceType       = executeDALIcommand('QueryDeviceType', DALIaddress)
        local ok14, byte8            = executeDALIcommand('QueryStatus', DALIaddress)

        ok = ok1 and ok2 and ok3 and ok4 and ok5 and ok6 and ok7 and ok8 and ok9 and ok10 and ok11 and ok12 and ok13 and ok14
        ok = ok and (lampPowerOn ~= nil) and maxLevel and actualLevel and minLevel and minPhysLevel and powerOnLevel and failureLevel
              and current and version and DTRcontents and (missingShortAddr ~= nil) and randomAddress and deviceType and byte8

        if (not ok) then return intro..'getDeviceInfo() failed"}', 'application/json' end

        if (membership == '') then membership = 'none' end

        -- fade time in seconds = 0.5*(2^n)^0.5  or  2^((n/2)-1)   where n = 0 to 15; (0.5 to 90.5 secs)
        local fadeTimeSecs = 0.5 * (2^current.fadeTime)^0.5
        local fadeTimeStr  = string.format('%-4ifade time in seconds:%5.1f', tostring(current.fadeTime), fadeTimeSecs)

        -- fade rate in steps per second = 506/(2^n)^0.5   where n = 1 to 254; (357.8 to 2.8 steps/secs)
        local stepsPerSec = 506/(2^current.fadeRate)^0.5
        local fadeRateStr = string.format('%-4isteps per second:%9.1f', tostring(current.fadeRate), stepsPerSec)

        local randomAddressStr = string.format('%i = 0x%06X', randomAddress, randomAddress)

        table.insert(deviceStatusTab, 'device at address:      '..DALIaddressStr)
        table.insert(deviceStatusTab, 'group membership is     '..membership..'\n')

        table.insert(deviceStatusTab, 'lamp power on?          '..tostring(lampPowerOn))
        table.insert(deviceStatusTab, 'maximum level           '..tostring(maxLevel))
        table.insert(deviceStatusTab, 'actual level            '..tostring(actualLevel))
        table.insert(deviceStatusTab, 'minimum level           '..tostring(minLevel))
        table.insert(deviceStatusTab, 'min physical level      '..tostring(minPhysLevel))
        table.insert(deviceStatusTab, 'power on level          '..tostring(powerOnLevel))
        table.insert(deviceStatusTab, 'failure level           '..tostring(failureLevel)..'\n')

        for i = 0, 15 do
            local ok, sceneLevel = executeDALIcommand('QuerySceneLevel', DALIaddress, i)
            if (ok and sceneLevel) then table.insert(deviceStatusTab, string.format('%-24s', 'scene level '..tostring(i))..tostring(sceneLevel)) end
        end

        table.insert(deviceStatusTab, '\ncurrent fade rate       '..fadeRateStr)
        table.insert(deviceStatusTab, 'current fade time       '..fadeTimeStr..'\n')

        table.insert(deviceStatusTab, 'version?                '..tostring(version))
        table.insert(deviceStatusTab, 'DTR contents            '..tostring(DTRcontents))
        table.insert(deviceStatusTab, 'missing short address?  '..tostring(missingShortAddr))
        table.insert(deviceStatusTab, 'random address is       '..randomAddressStr..'\n')

        table.insert(deviceStatusTab, 'device type is          '..tostring(deviceTypes[deviceType+1]))
        local stFlgs = getStatusFlags(byte8)
        for k, v in pairs(stFlgs) do
            table.insert(deviceStatusTab, string.format('%-24s', k)..tostring(v.b))
        end
    else
        table.insert(deviceStatusTab, 'No device found at address: '..DALIaddressStr)
    end

    debug('FINISHED the getDeviceInfo() command: all OK',50)
    local msg = table.concat(deviceStatusTab, '\n')
    return intro..escJSONentities(msg)..'"}', 'application/json'
end

-- a service in the implementation file
-- this can take some time to execute, so it is run as a job
-- example format 'Group10: 4,6,63' or 'Empty'
function getGroups()
    if (m_Busy) then return 4, nil else m_Busy = true end

    local addressList = luup.variable_get(PLUGIN_SID, 'Addresses', THIS_LUL_DEVICE) or ''

    local groupInfoList = {}
    for DALIaddress in addressList:gmatch('%d+') do
        local ok, membership = doQueryGroup(DALIaddress)
        if (ok) then
            for group in membership:gmatch('%d+') do
                group = tonumber(group)
                if (not groupInfoList[group]) then
                    groupInfoList[group] = DALIaddress
                else
                    groupInfoList[group] = groupInfoList[group]..','.. DALIaddress
                end
            end
        end
    end

    -- create/update the Vera variable for storing all the different addresses used by each group
    local allGroups = {}
    for group = 0, 15 do
        if ((groupInfoList[group] == nil) or (groupInfoList[group] == '')) then
            updateVariable('Group'..tostring(group), 'Empty')
            table.insert(allGroups, 'g'..tostring(group)..':e')
        else
            updateVariable('Group'..tostring(group), groupInfoList[group])
            table.insert(allGroups, 'g'..tostring(group)..':'..groupInfoList[group])
        end
    end
    updateVariable('AllGroups', table.concat(allGroups, ' '))

    debug('FINISHED the Get Groups command',50)
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- big overhead in reading 16 levels from potentially 64 devices, so run this as a job
-- example format: address.level: 'Scene4: 4.254,6.254,63.254' or 'Empty'
function getScenes()
    if (m_Busy) then return 4, nil else m_Busy = true end

    local addressList = luup.variable_get(PLUGIN_SID, 'Addresses', THIS_LUL_DEVICE) or ''

    local allScenes = {}
    for scene = 0, 15 do
        local sceneInfo = {}
        for DALIaddress in addressList:gmatch('%d+') do
            local ok, sceneLevel = executeDALIcommand('QuerySceneLevel', DALIaddress, scene)
            if (ok and sceneLevel and (sceneLevel ~= DALI_MASK)) then table.insert(sceneInfo, DALIaddress..'.'..tostring(sceneLevel)) end
        end

        -- create/update the Vera variable for storing all the found scene levels at the different addresses for each scene
        local sceneInfoList = table.concat(sceneInfo, ',')
        if ((sceneInfoList == nil) or (sceneInfoList == '')) then
            updateVariable('Scene'..tostring(scene), 'Empty')
            table.insert(allScenes, 's'..tostring(scene)..':e')
        else
            updateVariable('Scene'..tostring(scene), sceneInfoList)
            table.insert(allScenes, 's'..tostring(scene)..':'..sceneInfoList)
        end
    end
    updateVariable('AllScenes', table.concat(allScenes, ' '))

    debug('FINISHED the Get Scenes command',50)
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- this can take some time to execute, so it is run as a job.
-- delete = -1, no change = 0, add = +1
function setGroups()
    if (m_Busy) then return 4, nil else m_Busy = true end

    -- eg 'g0:e g1:e g2:e g3:0,1 g4:e g5:e g6:e g7:e g8:e g9:e g10:e g11:e g12:e g13:e g14:e g15:e'
    local changes = {}
    local allGroups = luup.variable_get(PLUGIN_SID, 'AllGroups', THIS_LUL_DEVICE) or ''
    -- [^%s] = everything but white space; + sign means 'one or more characters'
    for groupStr in string.gmatch(allGroups, '[^%s]+') do
        local first = true
        local groupAddress = -1
        for str in groupStr:gmatch('%d+') do
            local address = tonumber(str)
            if (first) then
                groupAddress = address
                changes[groupAddress] = {}
                first = false
            else -- default to removing all addresses that currently exist in each group
                changes[groupAddress][address] = -1
            end
        end
    end

    -- eg 'Group0: 4,7,63' .. 'Group15: 4,6,63' or 'Empty'
    for groupAddress = 0, 15 do
        local groupAddressStr = tostring(groupAddress)
         local groupList = luup.variable_get(PLUGIN_SID, 'Group'..groupAddressStr, THIS_LUL_DEVICE) or ''
        for str in groupList:gmatch('%d+') do
            local address = tonumber(str)
            if (changes[groupAddress][address]) then
                -- the address already exists and is marked for removal by default. Retain it instead.
                changes[groupAddress][address] = 0
            else -- the address doesn't already exist, so add it in.
                changes[groupAddress][address] = 1
            end
        end
     end

    local ok = true
    for groupAddress = 0, 15 do
        -- add and remove from each group as needed
        for address, change in pairs(changes[groupAddress]) do
            if (change == 1) then
                debug('add to group '..tonumber(groupAddress)..'; address: '..tostring(address),50)
                local ok1 = executeDALIcommand('AddToGroup', address, groupAddress)
                ok = ok and ok1
            elseif (change == -1) then
                debug('remove from group '..tonumber(groupAddress)..'; address: '..tostring(address),50)
                local ok2 = executeDALIcommand('RemoveFromGroup', address, groupAddress)
                ok = ok and ok2
            else
                debug('No change to group '..tonumber(groupAddress)..'; address: '..tostring(address),50)
            end
        end
    end

    if (not ok) then debug('setGroups() failed')
    else debug('FINISHED the Set Groups command',50) end
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- big overhead in writing 16 levels to potentially 64 devices, so run this as a job
function setScenes()
    if (m_Busy) then return 4, nil else m_Busy = true end

    -- eg s0:e s1:e s2:e s3:e s4:e s5:e s6:1.170,2.170 s7:e s8:e s9:e s10:e s11:e s12:e s13:e s14:e s15:e
    local changes = {}
    local allScenes = luup.variable_get(PLUGIN_SID, 'AllScenes', THIS_LUL_DEVICE) or ''
    -- [^%s] = everything but white space; + sign means 'one or more characters'
    for sceneStr in string.gmatch(allScenes, '[^%s]+') do
        local idx = 0
        local sceneNumber   = -1
        local deviceAddress = -1
        for str in sceneStr:gmatch('%d+') do
            local theNumbers = tonumber(str)
            if (idx == 0) then -- get the scene number
                sceneNumber = theNumbers
                changes[sceneNumber] = {}
            elseif(idx == 1) then -- get the device address
                deviceAddress = theNumbers
            elseif(idx == 2) then -- for this scene, for this device, save the scene level
                -- the level is saved as a negative value. This will flag it for deletion.
                changes[sceneNumber][deviceAddress] = -theNumbers
                idx = 0
            end
            idx = idx +1
        end
    end

    -- Three possibilities per scene:
    -- 1) remove device from scene. 2) change an existing device level. 3) add new device at a new level.
    -- get all the devices and their levels for each scene by
    -- parsing the scene info into an address/level array
    -- example format: address.level: 'Scene4: 4.254,6.254,63.254' or 'Empty'
    for sceneNumber = 0, 15 do
        local isKey      = true
        local address    = -1
        local addressLevelList = luup.variable_get(PLUGIN_SID, 'Scene'..sceneNumber, THIS_LUL_DEVICE) or ''
        for keysAndValues in addressLevelList:gmatch('%d+') do
            if (isKey) then
                address = tonumber(keysAndValues)
            else  -- value
                local sceneLevel = tonumber(keysAndValues)

                if   (changes[sceneNumber][address]
                and ((changes[sceneNumber][address] + sceneLevel) == 0)) then
                    -- the address with the required level already exists, so it will be retained.
                    -- Setting the array element to nil takes it out of the update process.
                    changes[sceneNumber][address] = nil
                    debug('No change to scene '..tonumber(sceneNumber)..'; address: '..tostring(address)..'; level: '..tostring(sceneLevel),50)
                else
                    -- the address already exists but with the wrong level.
                    -- or the address doesn't exist and needs to be added.
                    -- This will all be corrected in the update below.
                    changes[sceneNumber][address] = sceneLevel
                end
            end
            isKey = not isKey
        end
    end

    local ok = true
    for sceneNumber = 0, 15 do
        -- add and remove from each scene as needed
        for address, sceneLevel in pairs(changes[sceneNumber]) do
            if (sceneLevel >= 0) then
                debug('add to scene '..tonumber(sceneNumber)..'; address: '..tostring(address)..'; level: '..tostring(sceneLevel),50)
                local ok1 = transferViaDTR(sceneLevel, address, 'StoreDTRAsScene')
                ok = ok and ok1
            else -- flagged for deletion
                debug('remove from scene '..tonumber(sceneNumber)..'; address: '..tostring(address)..'; level: '..tostring(sceneLevel),50)
                local ok2 = executeDALIcommand('RemoveFromScene', address, sceneNumber)
                ok = ok and ok2
            end
        end
    end

    if (not ok) then debug('setScenes() failed')
    else debug('FINISHED the Set Scenes command',50) end
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- This task is typically allocated 15 minutes to execute.
-- Takes about 6 secs per device for a Tridonic gateway in mode 1.
-- We'll give it 10 minutes. It must be run as a job.
function setShortAddresses()
    if (m_Busy) then return 4, nil else m_Busy = true end

    -- get a flag array of existing short addresses
    local existingAddr = {}
    local addresses = luup.variable_get(PLUGIN_SID, 'Addresses', THIS_LUL_DEVICE) or ''
    for existing in addresses:gmatch('%d+') do
        existingAddr[tonumber(existing)] = true
    end

    -- get ready and start the initialisation timer
    -- method var:
    --    0x00 means program all devices regardless
    --    intermediate values allow short/group addressing
    --    0xff means program only those without a short address
    local method = 0xff
    executeDALIcommand('Initialise', method)

    -- command all devices to internally generate a 24 bit random address
    executeDALIcommand('Randomise')

    local MAX_SHORT_ADDRESS = 63
    local ourShortAddress   = MAX_SHORT_ADDRESS +1
    local devicesFoundCount = 0
    local addressTable      = {}

    -- Number the addresses starting at address 63 and works downwards. This way, it's easier
    -- to renumber the addresses later on, to match a physical layout of your own choosing,
    -- rather than using the initial random layout produced here.
    while (ourShortAddress > 0) do
        ourShortAddress = ourShortAddress -1

        if ((not existingAddr[ourShortAddress]) or (method ~= 0xff)) then

            local ok1, doneAllDevices = searchForDevices()
            if (not ok1) then debug('setShortAddresses(): search error') break end

            if (doneAllDevices) then break end

            -- Note: ProgramShortAddress and StoreDTRAsShortAddress expect the address
            -- in this format: 0AAA,AAA1  QueryShortAddress replies in the same format.
            -- so shift in the S flag in and out as needed
            local addrWithSbit = bitFunctions.lshift(ourShortAddress, 1)
            addrWithSbit = bitFunctions.bor(addrWithSbit, 0x01)

            -- if a ballast's random address matches the 3 byte search address, it internally
            -- becomes 'Selected'. It will now accept our supplied short address as its own.
            executeDALIcommand ('ProgramShortAddress', addrWithSbit)

            -- check that the short address is programmed OK. Only the 'Selected' device replies.
            -- 'Selected' means physically selected or searchAddress == randomAddress
            local ok2, DALIaddress = executeDALIcommand('QueryShortAddress')
            if (not (ok2 and DALIaddress and (DALIaddress ~= DALI_MASK))) then
                debug('setShortAddresses(): short address programming failed')
                break
            end

            -- shift out the S flag
            DALIaddress = bitFunctions.rshift(DALIaddress, 1)

            if (ourShortAddress ~= DALIaddress) then debug('setShortAddresses(): short address mismatch') break end

            -- success: tell the 'selected' ballast to withdraw from the addressing process
            debug('successfully programmed a device with short address: '..tostring(ourShortAddress),50)
            devicesFoundCount = devicesFoundCount +1
            executeDALIcommand('Withdraw')
        else
            debug('short address already in use: '..tostring(ourShortAddress),50)
        end

        table.insert(addressTable, tostring(ourShortAddress))

        -- if it's a lamp, perhaps flash the lamp at this point to indicate success?

    end  -- do while

    -- go to run mode
    executeDALIcommand('Terminate')

    -- create/update the Vera variable for storing all the found addresses
    table.sort(addressTable)
    addresses = table.concat(addressTable, ',')
    if (not ((addresses == nil) or (addresses == ''))) then
        updateVariable('Addresses', addresses)
    end

    debug('FINISHED the Set Short Addresses command: programmed '..tostring(devicesFoundCount)..' devices',50)

    -- the initialisation timer is still running but we can't shut it down
    m_Busy = false
    return 4, nil -- job Done
end

-- fade up and down to demo functionality
-- a service in the implementation file
function fadeUpDown(DALIaddress)
    debug('fading up/down')
    DALIaddress = tonumber(DALIaddress)

    if (m_fadeUp) then
        local ok1 = executeDALIcommand('DirectArcCommand', DALIaddress, DALI_MAX_LEVEL)
    else -- fade down
        local ok2 = executeDALIcommand('DirectArcCommand', DALIaddress, 0)
    end
    m_fadeUp = not m_fadeUp
end

-- stop fading up and down to demo functionality
-- a service in the implementation file
function stopFading(DALIaddress)
    debug('stop fading')
    DALIaddress = tonumber(DALIaddress)

    executeDALIcommand('DirectArcCommand', DALIaddress, DALI_MASK)
end

-- update the dimmer's LoadLevelStatus
local function queryActualLoadLevelStatus(lul_device)
    local DALIaddress = getDALIaddress(lul_device)
    local ok, theLevel = executeDALIcommand('QueryActualLevel', DALIaddress)

    if (not ok) then debug('queryActualLoadLevelStatus() failed') return false end

    local actualLevel = theLevel
    if (theLevel == nil) then
        debug('queryActualLoadLevelStatus(): device at address '..tostring(DALIaddress)..' is probably not powered on',50)
        actualLevel = 0
    end

    local percent = math.ceil((actualLevel / DALI_MAX_LEVEL) * 100.0)
    updateDeviceStatus(percent, true, lul_device)

    if (theLevel == nil) then return false end

    return true
end

--[[
-- a service in the implementation file
-- action:  do the DIMMING SetLoadLevelTarget
function setLoadLevelTarget(lul_device, targetValue)
    targetValue = tonumber(targetValue)
    local ok1 = true
    local ok2 = true
    local ok3 = true

    local DALIaddress = getDALIaddress(lul_device)

    if (targetValue == 0) then
        ok1 = executeDALIcommand('Off', DALIaddress)
    elseif (targetValue == 100) then
        ok2 = executeDALIcommand('RecallMaxLevel', DALIaddress)
    elseif ((targetValue > 0) and (targetValue < 100)) then

        local arcValue = math.floor((targetValue/100) * DALI_MAX_LEVEL)
        ok3 = executeDALIcommand('DirectArcCommand', DALIaddress, arcValue)
    else
        ok1 = false
        debug('invalid TargetValue in setLoadLevelTarget()')
    end

    if (not (ok1 and ok2 and ok3)) then debug('setLoadLevelTarget() failed') return false end

    -- HACK calling queryActualLoadLevelStatus() while a lamp is fading up or down results  in the
	-- immediate fade results being returned, so we can't use this command unless we know
	-- that the fade has finished
    -- queryActualLoadLevelStatus(lul_device)
    updateVariable('LoadLevelStatus', tostring(targetValue), SWD_SID, lul_device)

    return true
end

An attempt to account for the minPhysLevel offset. It's unresponsive:

-- a service in the implementation file
-- update the DIMMER's LoadLevelStatus
function queryActualLoadLevelStatus(lul_device)
    local DALIaddress = getDALIaddress(lul_device)
    -- HACK to improve the responsivity of this action, max & phys values should probably be held as Vera vars
    local ok1, maxLevel     = executeDALIcommand('QueryMaxLevel',         DALIaddress)
    local ok2, actualLevel  = executeDALIcommand('QueryActualLevel',      DALIaddress)
    local ok3, minPhysLevel = executeDALIcommand('QueryPhysicalMinLevel', DALIaddress)

    if (not (ok1 and ok2 and ok3)) then debug('queryActualLoadLevelStatus() failed') return false end

    local percent = math.ceil(((actualLevel - minPhysLevel) / (maxLevel - minPhysLevel)) * 100)
    updateVariable('LoadLevelStatus', tostring(percent), SWD_SID, lul_device)
    return true
end

-- a service in the implementation file
-- action:  do the DIMMING SetLoadLevelTarget
function setLoadLevelTarget(lul_device, targetValue)
    targetValue = tonumber(targetValue)
    local ok1 = true
    local ok2 = true
    local ok3 = true

    local DALIaddress = getDALIaddress(lul_device)

    if (targetValue == 0) then
        ok1 = executeDALIcommand('Off', DALIaddress)
    elseif (targetValue == 100) then
        ok2 = executeDALIcommand('RecallMaxLevel', DALIaddress)
    elseif ((targetValue > 0) and (targetValue < 100)) then
        -- HACK to improve the responsivity of this action, max & phys values should probably be held as Vera vars
        ok1, maxLevel     = executeDALIcommand('QueryMaxLevel', DALIaddress)
        ok2, minPhysLevel = executeDALIcommand('QueryPhysicalMinLevel', DALIaddress)

        local arcValue = math.floor(((targetValue/100) * (maxLevel - minPhysLevel)) + minPhysLevel)
        ok3 = executeDALIcommand('DirectArcCommand', DALIaddress, arcValue)
    else
        ok1 = false
        debug('invalid TargetValue in setLoadLevelTarget()')
    end

    if (not (ok1 and ok2 and ok3)) then debug('setLoadLevelTarget() failed') return false end
    queryActualLoadLevelStatus(lul_device)
    return true
end

-- a service in the implementation file
-- do the ON/OFF action
function setTarget(lul_device, targetValue)
    local HA_SID      = 'urn:micasaverde-com:serviceId:HaDevice1'

    local DALIaddress = getDALIaddress(lul_device)
    local DALIcommand = 'Off'  -- with no fade
    local status      = '0'

    -- check if the command should be reversed for this device
    local lul_reverse = luup.variable_get(HA_SID, 'ReverseOnOff', lul_device)

    if ((targetValue == '1') or ((targetValue == '0') and (lul_reverse == '1'))) then
        DALIcommand = 'RecallMaxLevel'  -- with no fade
        status = '1'
    end

    local ok = executeDALIcommand(DALIcommand, DALIaddress)

    if (not ok) then debug('setTarget() failed') return false end
    updateVariable('Status', status, SWP_SID, lul_device)
    return true
end
]]

-- a service in the implementation file
-- do the DIMMING action
-- If the DirectArcCommand returns OK, we assume the level change does in fact occur
-- and we update the LoadLevelStatus var to match. If we checked the actual light status
-- we would have to wait till any fade operations completed in order to get the correct
-- status. For groups; we would potentially  have to interrogate a lot of lights as well.
-- That's too much of an effort.
function setLoadLevelTarget(lul_device, targetValue)
    targetValue = tonumber(targetValue)

    local arcValue = 0
    if (targetValue == 0) then
        arcValue = 0
    elseif (targetValue == 100) then
        arcValue = DALI_MAX_LEVEL
    elseif ((targetValue > 0) and (targetValue < 100)) then
        arcValue = math.floor((targetValue/100) * DALI_MAX_LEVEL)
    else
        debug('invalid TargetValue in setLoadLevelTarget()')
        return false
    end

    if (not luup.devices[lul_device].id:find('Group')) then
	    -- device is just a single light. Update the light and its status.
        local DALIaddress = getDALIaddress(lul_device)
        local ok = executeDALIcommand('DirectArcCommand', DALIaddress, arcValue)
        if (not ok) then debug('setLoadLevelTarget() failed') return false end
		updateDeviceStatus(targetValue, true, lul_device)

    else -- device is a group of lights. Each light and its status needs to be updated.
        local groupAddress = luup.devices[lul_device].id:match('%d+')
        if (not (groupAddress and tonumber(groupAddress))) then debug('setLoadLevelTarget() failed') return false end
        debug('groupAddress = '..groupAddress)

        -- update the status of the group device. It doesn't have or a need for a 'Watts' variable
        local ok = executeDALIcommand('DirectArcCommand', tonumber(groupAddress) + GROUP_OFFSET, arcValue)
        if (not ok) then debug('setLoadLevelTarget() failed') return false end
		updateDeviceStatus(targetValue, false, lul_device)

        -- for all the lights in the group device; update their status
        local groupList = luup.variable_get(PLUGIN_SID, 'Group'..tostring(groupAddress), THIS_LUL_DEVICE) or ''
        for groupDevice in groupList:gmatch('%d+') do
            for deviceID, v in pairs(luup.devices) do
                -- v.device_num_parent is a number, v.id is a string, deviceID is a number
                if ((v.device_num_parent == THIS_LUL_DEVICE) and (v.id == tostring(groupDevice))) then
		            updateDeviceStatus(targetValue, true, deviceID)
                end
            end
        end
    end
    return true
end

-- a service in the implementation file
-- do the ON/OFF action
function setTarget(lul_device, targetValue)
    local ok = false
    targetValue = tonumber(targetValue)
    if (targetValue == 0) then
        ok = setLoadLevelTarget(lul_device, 0)
    elseif (targetValue == 1) then
        ok = setLoadLevelTarget(lul_device, 100)
    end

    if (not ok) then debug('setTarget() failed') return false end
    return true
end

--[[
a service in the implementation file
action:  execute DALI scene

Sixrteen scenes can be set up. When a scene command is sent, all DALI devices check to see if they are
included in that particular scene. If they are part of the scene, then the DALI device reacts accordingly.
]]
function runScene(cmdValueStr, arcSceneGroupOffsetStr)
    local ok  = true
    local sceneAddress = tonumber(cmdValueStr)
    local sceneNumber  = tonumber(arcSceneGroupOffsetStr)
    if (not(sceneAddress and sceneNumber and (sceneNumber >= 0) and (sceneNumber <= 15))) then
        debug('runScene(): parameter error')
        return false
    end

    -- get all the devices and their levels for this scene by
    -- parsing the scene info into an address/level array
    local addrLev    = {}
    local isKey      = true
    local address    = -1
    local arrayEmpty = true
    local addressLevelList = luup.variable_get(PLUGIN_SID, 'Scene'..arcSceneGroupOffsetStr, THIS_LUL_DEVICE) or ''
    for keysAndValues in addressLevelList:gmatch('%d+') do
        if (isKey) then
            address = tonumber(keysAndValues)
        else  -- value
            addrLev[address] = tonumber(keysAndValues)
            arrayEmpty = false
        end
        isKey = not isKey
    end

    -- empty scene?
    if (arrayEmpty) then return ok end

    -- this is the easy bit. Later we have to update all the levels for Vera!
    ok = executeDALIcommand('GoToScene', sceneAddress, sceneNumber)
    if (not ok) then return ok end

    -- filter the devices/levels list to suit: a) single device, b) group of devices, c) broadcast
    filteredResult = {}
    if (sceneAddress < GROUP_OFFSET) then -- single device in the scene
        filteredResult[address] = addrLev[address]
    elseif (sceneAddress < (GROUP_OFFSET + 16)) then -- just the group devices in the scene
        local groupAddress = sceneAddress - GROUP_OFFSET
        -- HACK debug ('groupAddress = '..tostring(groupAddress))
        local groupList = luup.variable_get(PLUGIN_SID, 'Group'..tostring(groupAddress), THIS_LUL_DEVICE) or ''
        -- HACK debug ('groupList = '..groupList)
        for addr, lev in pairs(addrLev) do
            for groupDevice in groupList:gmatch('%d+') do
                if (tonumber(groupDevice) == addr) then
        -- HACK debug ('added '..tostring(addr)..': '..tostring(lev))
                    filteredResult[addr] = lev
                end
            end
        end
    else  -- do scene broadcast, no filtering required
        filteredResult = addrLev
    end

    for addr, lev in pairs(filteredResult) do
        local lul_device = nil
        for deviceID, v in pairs(luup.devices) do
            -- v.device_num_parent is a number, v.id is a string, deviceID is a number
            if ((v.device_num_parent == THIS_LUL_DEVICE) and (v.id == tostring(addr))) then lul_device = deviceID end
        end

        local percent = math.ceil((lev / DALI_MAX_LEVEL) * 100)
        -- HACK debug('device id: '..tostring(lul_device)..', percent = '..tostring(percent))
        updateDeviceStatus(percent, true, lul_device)
    end

    return ok
end

-- a service in the implementation file
-- send a single command to the DALI gateway - primarily for testing
-- function needs to be global
-- Typically value1 is a DALIaddress and value2 is optional associated data
-- Note however; some commands do not require value1 and value2 to be supplied eg see function cmdValueRequired()
function DALIcommand(cmdStr, value1, value2)
	-- lower levels will validate all the passed parameters
    local ok, result = executeDALIcommand(cmdStr, value1, value2)
    if (not ok) then debug('DALIcommand error detected - refer to previous log entries for finer detail') end
    return ok, result
end

-- a service in the implementation file
-- change a DALI short address. Code ensures duplicates are not created.
function changeShortAddress(oldDALIaddressStr, newDALIaddressStr)
    local oldDALIaddress = tonumber(oldDALIaddressStr)
    local newDALIaddress = tonumber(newDALIaddressStr)
    local ok = false

    if (not (oldDALIaddress and   (oldDALIaddress >= 0) and (oldDALIaddress <= 63))) then return ok end
    if (not (newDALIaddress and (((newDALIaddress >= 0) and (newDALIaddress <= 63)) or (newDALIaddress == DALI_MASK)))) then return ok end

    -- get a flag array of existing short addresses
    local existingAddr = {}
    local addresses = luup.variable_get(PLUGIN_SID, 'Addresses', THIS_LUL_DEVICE) or ''
    for existing in addresses:gmatch('%d+') do
        existingAddr[tonumber(existing)] = true
    end

    -- guard against creating duplicates
    if (existingAddr[newDALIaddress]) then
        debug('FINISHED the Change Short Address command. ERROR: new address is already in use. Try again.',50)
        return ok
    end

    --[[ HACK: probably not required. There may be a valid old address but it may not be known by Vera.
    -- guard against invalid old address
    if (not existingAddr[oldDALIaddress]) then
        debug('FINISHED the Change Short Address command. ERROR: old address not found. Try again.',50)
        return ok
    end
    ]]

    -- shift in the S flag: format is: 0AAA AAA1 or 1111 1111 (DALI_MASK)
    local newDALIaddressBitS = bitFunctions.lshift(newDALIaddress, 1)
    newDALIaddressBitS = bitFunctions.bor(newDALIaddressBitS, 0x01)

    -- confine to 8 bits: a left shift of DALI_MASK overflows the byte
    newDALIaddressBitS = bitFunctions.band(newDALIaddressBitS, 0xFF)

    local ok = transferViaDTR(newDALIaddressBitS, oldDALIaddress, 'StoreDTRAsShortAddress')
    if (not ok) then
        debug('changeShortAddress(): change of address failed - old DALI address may be invalid?',50)
        return ok
    end

    existingAddr[oldDALIaddress] = nil

    -- suppling DALI_MASK as the new address just erases the old address, so check for it
    if (newDALIaddress ~= DALI_MASK) then existingAddr[newDALIaddress] = true end

    local addressTable = {}
    for k, v in pairs(existingAddr) do
       table.insert(addressTable, k)
    end

    -- update the Vera variable for storing all the device addresses
    table.sort(addressTable)
    addresses = table.concat(addressTable, ',')

    if (not addresses) then addresses = '' end
    updateVariable('Addresses', addresses)

    debug('FINISHED the Change Short Address command - OK',50)
    return ok
end

-- a service in the implementation file
-- action:  read all the fade rates and times
function getFadeValues()
    if (m_Busy) then return 4, nil else m_Busy = true end
    local ok = true

    for light in daliLights() do
        local DALIaddress = getDALIaddress(light)
        local ok1, current = executeDALIcommand('QueryFadeTimeRate', DALIaddress)

        if (ok1 and (current ~= nil)) then
            updateVariable('FadeTime', tostring(current.fadeTime), PLUGIN_SID, light)
            updateVariable('FadeRate', tostring(current.fadeRate), PLUGIN_SID, light)
        elseif (current == nil) then
            debug('fadeChange(): device at address '..tonumber(DALIaddress)..' is probably not powered on')
            ok = false
        else
            ok = false
        end
    end

    if (not ok) then debug('getFadeValues() failed')
    else debug('FINISHED the Get Fade Values command',50) end
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- action:  write all the fade rates and times
function setFadeValues()
    if (m_Busy) then return 4, nil else m_Busy = true end
    local ok = true

    for light in daliLights() do
        local newFadeTime = luup.variable_get(PLUGIN_SID, 'FadeTime', light)
        local newFadeRate = luup.variable_get(PLUGIN_SID, 'FadeRate', light)

        newFadeTime = tonumber(newFadeTime)
        newFadeRate = tonumber(newFadeRate)

        if ((newFadeTime ~= nil) and (newFadeRate ~= nil)) then
            local ok1 = fadeChange(light, newFadeTime, newFadeRate)
            ok = ok and ok1
        else
            ok = false
        end
    end

    if (not ok) then debug('setFadeValues() failed')
    else debug('FINISHED the Set Fade Values command',50) end
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- action:  read all the power on levels
function getPowerOnLevels()
    if (m_Busy) then return 4, nil else m_Busy = true end
    local ok = true

    for light in daliLights() do
        local DALIaddress = getDALIaddress(light)
        local ok1, currentPowerOn = executeDALIcommand('QueryPowerOnLevel', DALIaddress)

        if (ok1 and (currentPowerOn ~= nil)) then
            updateVariable('PowerOnLevel', tostring(currentPowerOn), PLUGIN_SID, light)
        elseif (currentPowerOn == nil) then
            debug('getPowerOnLevels(): device at address '..tonumber(DALIaddress)..' is probably not powered on')
            ok = false
        else
            ok = false
        end
    end

    if (not ok) then debug('getPowerOnLevels() failed')
    else debug('FINISHED the Get Power On Levels command',50) end
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- action:  write all the power on levels
function setPowerOnLevels()
    if (m_Busy) then return 4, nil else m_Busy = true end
    local ok = true

    for light in daliLights() do
        local newPowerOn = luup.variable_get(PLUGIN_SID, 'PowerOnLevel', light)
        newPowerOn = tonumber(newPowerOn)

        if (newPowerOn ~= nil) then
            local DALIaddress = getDALIaddress(light)
            local ok1 = transferViaDTR(newPowerOn, DALIaddress, 'DTRAsPowerOnLevel')
            ok = ok and ok1
        else
            ok = false
        end
    end

    if (not ok) then debug('setPowerOnLevels() failed')
    else debug('FINISHED the Set Power On Levels command',50) end
    m_Busy = false
    return 4, nil -- job Done
end

-- a service in the implementation file
-- just for testing - nothing else
function runTest(value1, value2, value3)
    DEBUG_MODE = true

    if (value1) then debug('value1: '..value1) else debug('value1 is nil') end
    if (value2) then debug('value2: '..value2) else debug('value2 is nil') end
    if (value3) then debug('value3: '..value3) else debug('value3 is nil') end

    -- check type 6 device
    --local ok1 = executeDALIcommand('EnableTypeX', 6)
    --local ok2 = executeDALIcommand('T6QueryFeatures', tonumber(value1))

    -- mix RGB values
    arcValue1 = tonumber(value1)
    arcValue2 = tonumber(value2)
    arcValue3 = tonumber(value3)
    executeDALIcommand('DirectArcCommand', 3, arcValue1)
    executeDALIcommand('DirectArcCommand', 4, arcValue2)
    executeDALIcommand('DirectArcCommand', 5, arcValue3)

    DEBUG_MODE = luup.variable_get(PLUGIN_SID, 'DebugEnabled', THIS_LUL_DEVICE)
end

-- Prod the DALI gateway device. Function needs to be global.
-- We do this because communications will shut down on some platforms (eg RasPi but not on a Vera 3) unless regularly prodded.
-- This may all be related to the settings used in the /etc/sysctl.conf file ??:
-- Vera 3 sets the file to contain: net.ipv4.tcp_keepalive_time=120
-- The usual defaults are: tcp_keepalive_time = 7200 (seconds) tcp_keepalive_intvl = 75 (seconds) tcp_keepalive_probes = 9 (number of probes)
-- Note that the CheckGateway command performs no action on the actual DALI bus
function runHeartBeat()
    if (m_HeartBeatEnable ~= '1') then return end

    local ok = executeDALIcommand('CheckGateway')
    if (not ok) then
        debug('DALI heart beat: gateway did not reply - possible loss of communications with gateway.')
    end

    -- prod the gateway regularly
    luup.call_delay('runHeartBeat', m_HeartBeatInterval)
end

-- web page for the device status
local function htmlIntroPage()
    local title  = 'DALI Planet'
    local header = 'DALI Planet ver: '..PLUGIN_VERSION

    local DALIinfoTab = {}   -- all in a pre tag so use linefeeds, not html breaks

    table.insert(DALIinfoTab, 'Number of groups: '..tostring(m_GroupCount))
    table.insert(DALIinfoTab, 'Number of lights: '..tostring(m_LightCount)..'   - RGBW LED strips count as 4 lights')
    table.insert(DALIinfoTab, 'Unpowered lights: '..tostring(m_UnpoweredCount)..'\n')

    table.insert(DALIinfoTab, 'The DALI devices listed here and in bold below, were probably not powered on, when the Luup engine was started:')
    local unpoweredStr = table.concat(m_UnpoweredLights,',')..',\n'

    table.insert(DALIinfoTab, unpoweredStr)
	table.insert(DALIinfoTab, ' Id   Description                           Room                  Watts   fr   ft')

	local wattsTotal = 0
    for k, v in pairs(luup.devices) do
        -- we're only interested in the DALI devices
        if (v.device_num_parent == THIS_LUL_DEVICE) then
		    -- note that 'groups' will be displayed but they may not have all vars set or even available
		    local fadeRate = luup.variable_get(PLUGIN_SID, 'FadeRate', k) or 'na'
		    local fadeTime = luup.variable_get(PLUGIN_SID, 'FadeTime', k) or 'na'
		    local watts    = luup.variable_get(ENERGY_METERING_SID, 'Watts', k)
			local watts = tonumber(watts) or 0
			wattsTotal = wattsTotal + watts
			local line = string.format('%3i   %-36s  %-20s  %5.1f   %2s   %2s', k, v.description, luup.rooms[v.room_num], watts, fadeRate, fadeTime)
		    if (string.find(unpoweredStr,k..',')) then
			    table.insert(DALIinfoTab, '<b>'..line..'</b>')
			else
			    table.insert(DALIinfoTab, line)
			end
		end
    end
	table.insert(DALIinfoTab, string.format('\nTotal Watts: %.1f', wattsTotal))

    local strTab = {
    htmlHeader(),
    '<title>'..title..'</title>',
    htmlJavaScript(),
    '</head>\n',
    '<body>',
    '<h3>'..header..'</h3>',
    '<div>',
    'Enter a DALI address --> <input id="daliAddressID" type="text" name="daliAddress" value=""/>',
    '<input id="submitBtnID" type="button" name="submitBtn" value="Submit"/><br/><br/>',
    '<pre id="deviceStatusID">',
    '</pre>',
	'<hr/>',
    '<pre>',
    table.concat(DALIinfoTab, '\n'),
    '</pre>',
	'<hr/><br/>',
    '</div>',
    '</body>',
    '</html>'
    }

    return table.concat(strTab,'\n'), 'text/html'
end

-- entry point for all html page requests and all ajax function calls
-- http://vera_ip_address/port_3480/data_request?id=al_info
function requestMain (lul_request, lul_parameters, lul_outputformat)
    debug('request is: '..tostring(lul_request))
    for k, v in pairs(lul_parameters) do debug ('parameters are: '..tostring(k)..'='..tostring(v)) end
    debug('outputformat is: '..tostring(lul_outputformat))

    if not (lul_request:lower() == PLUGIN_URL_ID) then return end

    -- set the parameters key and value to lower case
    local lcParameters = {}
    for k, v in pairs(lul_parameters) do lcParameters[k:lower()] = v:lower() end

    -- output the intro page?
    if not lcParameters.fnc then
        if (m_Busy) then return '' else m_Busy = true end
        local page = htmlIntroPage()
        m_Busy = false
        return page
    end -- no 'fnc' parameter so do the intro

    if (lcParameters.fnc == 'getdeviceinfo') then return getDeviceInfo(lcParameters) end

    return '{}', 'application/json'
end

-- start up the plugin
-- Refer to: I_DaliPlanetPSS1.xml
-- <startup>luaStartUp</startup>
-- Function must be global
function luaStartUp(lul_device)
    THIS_LUL_DEVICE = lul_device
    debug('initialising plugin: '..PLUGIN_NAME)

    -- Lua ver 5.1 does not have bit functions, whereas ver 5.2 and above do
    debug('Using: '.._VERSION)

    if (bitFunctions == nil) then
        debug('bit library not found\n')
        return false, 'Bit library not found', PLUGIN_NAME
    end

    -- set up some defaults:
    updateVariable('PluginVersion', PLUGIN_VERSION)

    -- set up some defaults:
    local debugEnabled = luup.variable_get(PLUGIN_SID, 'DebugEnabled', THIS_LUL_DEVICE)
    if ((debugEnabled == nil) or (debugEnabled == '')) then
        debugEnabled = '0'
        updateVariable('DebugEnabled', debugEnabled)
    end
    DEBUG_MODE = (debugEnabled == '1')

    local pluginEnabled = luup.variable_get(PLUGIN_SID, 'PluginEnabled', THIS_LUL_DEVICE)
    if ((pluginEnabled == nil) or (pluginEnabled == '')) then
        pluginEnabled = '1'
        updateVariable('PluginEnabled', pluginEnabled)
    end

    -- Vera doesn't need the heartbeat. Note however RasPI does.
    local heartBeatEnable = luup.variable_get(PLUGIN_SID, 'HeartBeatEnable', THIS_LUL_DEVICE)
    if ((heartBeatEnable == nil) or (heartBeatEnable == '')) then
        -- Set the heartBeat to on. Vera doesn't need it but it does no harm.
		-- The user can turn it off if they so wish later.
        heartBeatEnable = '1'
        updateVariable('HeartBeatEnable', heartBeatEnable)
    end
    m_HeartBeatEnable = heartBeatEnable

    -- don't allow the heartbeat to be any faster than twenty minutes.
	-- any shorter than 30 minutes seems to fail on a RasPi
    local heartBeatInterval = luup.variable_get(PLUGIN_SID, 'HeartBeatInterval', THIS_LUL_DEVICE)
    local theInterval = tonumber(heartBeatInterval)
    if ((theInterval == nil) or (theInterval < TWENTY_MINUTES)) then
        theInterval = TWENTY_MINUTES
        updateVariable('HeartBeatInterval', tostring(theInterval))
    end
    m_HeartBeatInterval = theInterval

    -- the user must enter a gateway type
    local gatewayType = luup.variable_get(PLUGIN_SID, 'GatewayType', THIS_LUL_DEVICE) or ''
    if (gatewayType == '') then
        -- first time round, this will create the variable but
        -- it remains invalid; the user must set it
        luup.variable_set(PLUGIN_SID, 'GatewayType', gatewayType, THIS_LUL_DEVICE)
    end

    -- select hardware: CL_DIDIO, TRIDONIC_SCI_1, etc
    local invalidGateway = setGatewayType(gatewayType)
    if (invalidGateway) then return false, 'The gateway selection is invalid', PLUGIN_NAME end

    if (pluginEnabled ~= '1') then return true, 'All OK', PLUGIN_NAME end

    -- registers a handler for the functions called via ajax
    luup.register_handler('requestMain', PLUGIN_URL_ID)

    local ipa = luup.devices[THIS_LUL_DEVICE].ip
    local ipAddress = ipa:match('^(%d%d?%d?%.%d%d?%d?%.%d%d?%d?%.%d%d?%d?)')
    local ipPort    = ipa:match(':(%d+)$')

    if (ipAddress and (ipAddress ~= '')) then
        if (not ipPort) then ipPort = IP_PORT end

        luup.io.open (THIS_LUL_DEVICE, ipAddress, ipPort)
        debug('DALI startup: running on IP address '..ipAddress..' port '..ipPort)
    else
        debug('DALI startup: running on serial')
    end

    local ok = executeDALIcommand('CheckGateway')
    if (not ok) then
        debug('DALI startup: gateway not currently available. Plugin exiting.')
        return false, 'DALI gateway not ready', THIS_LUL_DEVICE
    end

    local CATEGORY_GENERIC_IN_OUT = '11'
    luup.attr_set('category_num', CATEGORY_GENERIC_IN_OUT, THIS_LUL_DEVICE)

    local addressList = luup.variable_get(PLUGIN_SID, 'Addresses', THIS_LUL_DEVICE)

    -- first time round create and set the var to empty
    if (addressList == nil) then
        addressList = ''
        updateVariable('Addresses', addressList)
    end

    -- make a child for each DALIaddress found in Addresses created by the setShortAddresses()
    local DIMMABLE_LIGHT_FILE = 'D_DimmableLight1.xml'
    local child_devices = luup.chdev.start(THIS_LUL_DEVICE)

    -- this will add and/or remove devices depending on addressList (which may be an empty string)
    for DALIaddress in addressList:gmatch('%d+') do
        luup.chdev.append(
            THIS_LUL_DEVICE,
            child_devices,
            DALIaddress,  -- altid
            'DALI address '..DALIaddress,
            DIMMABLE_LIGHT_DEV,    -- device type
            DIMMABLE_LIGHT_FILE,   -- device filename
            '',     -- implementation filename
            '',     -- parameters
            false)  -- embedded
		m_LightCount = m_LightCount+1
    end

    -- do the groups as well
    -- this will add and/or remove groups depending on groupList (which may be an empty string)
    for groupAddress = 0, 15 do
        local groupAddressStr = tostring(groupAddress)
        local groupList = luup.variable_get(PLUGIN_SID, 'Group'..groupAddressStr, THIS_LUL_DEVICE) or ''
        if (groupList:find('%d+')) then
            luup.chdev.append(
                THIS_LUL_DEVICE,
                child_devices,
                'Group'..groupAddressStr,  -- altid
                'DALI group '..groupAddressStr,
                DIMMABLE_LIGHT_DEV,    -- device type
                DIMMABLE_LIGHT_FILE,   -- device filename
                '',     -- implementation filename
                '',     -- parameters
                false)  -- embedded
	    m_GroupCount = m_GroupCount+1
        end
    end
    luup.chdev.sync(THIS_LUL_DEVICE, child_devices)

    -- can't continue until the user runs the setShortAddresses(),
    -- which fills in the 'Addresses' variable as appropriate
    if (addressList == '') then
        debug('you need to run Set Addresses, to get this plugin to work!')
        return true, 'All OK', PLUGIN_NAME
    end

--------------------------------------------------------------------------------

    setPowerConsumption(10.0)

    -- update the current level status for each light
    for light in daliLights() do
        local ok1 = queryActualLoadLevelStatus(light)

        if (not ok1) then
		    m_UnpoweredCount = m_UnpoweredCount+1
            table.insert(m_UnpoweredLights, tostring(light))
        end
    end

    -- prod the gateway regularly if enabled
	-- this ensures the comms to the gateway stays open
    runHeartBeat()

    -- required for UI7. UI5 uses true or false for the passed parameter.
    -- UI7 uses 0 or 1 or 2 for the parameter. This works for both UI5 and UI7
    luup.set_failure(false)

    return true, 'All OK', PLUGIN_NAME
end

--return true
