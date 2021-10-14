DECLARE SUB SGCCS (NXA%, SXA%, X%, XS%, TD%, PGCC%)
DECLARE SUB SWLOCKS ()
DECLARE SUB TestSignals ()
DECLARE SUB SMINItest ()
DECLARE SUB ABSIGNALS ()
DECLARE SUB Signals ()
DECLARE SUB CRTDISPLAY ()
DECLARE SUB HEADER ()
DECLARE SUB READRR ()
DECLARE SUB WRITERR ()
DECLARE SUB TESTOUTPUTS ()
DECLARE SUB INITRR ()
DECLARE SUB CTCBOARD ()
DEFINT A-Z
DECLARE SUB INIT ()
DECLARE SUB OUTPUTS ()
DECLARE SUB INPUTS ()
DECLARE SUB RXBYTE ()
DECLARE SUB TXPACK ()
DECLARE SUB FastClk ()
DECLARE SUB SPEEDTEST ()
DECLARE SUB TIMERCNT ()


REM**CMRI PROGRAM USING CALL STATEMENTS** Apr 2005 JMJ, modified Oct-14-2008, FEB-5-2011,
' 31-Dec-2015 added I/O cards 6 & 7 Latonia and associated I/O control software.
' 24-Feb=2016 added SMINI UA=1 Walton 28-Feb-2016 inputs blk(25-36)
' 3-Mar-2016 changed push button variable naming all to PB(??) for consistemcy
' 31-Mar-2016 added fast clock module
' 10-Jly-2016 added speed test module
'  5-Oct-2016 added SMINI #2 UA-2 for Sparta
' 28-Jan-2017 bug fix interlock DeCoursey Yard Throat
' 28-Jan-2017 added menu for start up select and go direct to desired operation
' 19-Mar-2017 added software for switch locks, request for InHand
' 19-JUN-2017 added TIMERCNT sub utility to execute multiple time delays
' 17-JLY-2017 improved SPEED TEST sub. Cosmetics, LEDs, on screen info...
' 21-AUG-2017 added controlled electric switch locks 57-63
' 21-Aug-2017 added controlled electric switch locks 39-41
'  4-SEP-2017 refined speed test to index LEDs for laps 1-5
' 30-Sep-2017 added manual switch lock 59
' 18-Feb-2018 added SMINI #3 Worthville, locking switch panels 37-29
' 14-Mar-2018 increased Timer Counts from 65 to 75. Set all switches N on startup
'  8-Jly-2018 began writing signal software created  SUB ABSIGNALS
'  1-Nov-2018 more signal software, signal bridge at Wothhville, cosmetics speed test
' 22-Jan-2019 create routine to test new SMINI boards before placing in service.
'  7-Mar-2019 remove code to set Switch motors N on startup
' 17-Mar-2019 add subroutine to test all signals
' 20-Aug-2019 moved I/O from SUSIC 0 to SMINI 5
' 2-Dec-2019 added signals Latonia, Sparta & Worthville
' 2-Mar-2020 corrected signal logic Sparta
' 16-Mar-2020 added crossing protection Worthville
' 26-Aug-2020 reconcilled switch numbers (deCoursey & Latonia yards)
' 28-Aug-2020 added switch locks Campbellsburg
' 10-Oct-2020 reconcilled SW#, improved CTR display
' 22-Oct-2020 added SIGL(31) & SIGR(30), added monitor for loop time
' 11-DEC-2020 added grad crossing control logic
' 26-JAN-2021 option to have or void aproach lighting. often useful in testing
' 3-May-2021 added indicator Latonia pane4l to monitor SW(55)
' 10-August-2021 changed software to meet changes in DeCoursey  yard
' 11-Oct-2021 added kill relays to DeCoursey yard Relay(1-7)

REM**GLOBALIZE SERIAL PROTOCOL HANDLING VARIABLES
   DIM SHARED OB(60), IB(60), CT(15), TB(80), CLOR(173), Relay(10)
   COMMON SHARED UA, COMPORT, BAUD100, NDP$, DL, NS, NI, NO, MAXTRIES
   COMMON SHARED INBYTE, ABORTIN, INTRIES, INITERR, PA, LM, MT
REM**GLOBALIZE CONSTANTS FOR PACKING AND UNPACKING I/O BYTES
     COMMON SHARED B0, B1, B2, B3, B4, B5, B6, B7
     COMMON SHARED W1, W2, W3, W4, W5, W6, W7
REM** GLOBALIZE RR DEVICES
     COMMON SHARED PB, PB#, PBP, TGR, TGN, TUN, TUR, OCC, DRK, RED, GRN, YEL, FRED, FGRN, REDB, YELB, GRNB, REDRED, REDGRN, GRNRED, YELRED, REDYEL, REDREDB, REDGRNB, GRNREDB, YELREDB, REDYELB, FREDB, FREDB1, FREDB2, REDFRED, REDFRED1, REDFRED2,  _
FREDGRN, FREDGRN1, FREDGRN2, NORTH, SOUTH
     COMMON SHARED REDREDREDB, GRNREDREDB, YELREDREDB, REDGRNREDB, REDYELREDB, REDREDYELB, REDREDFYELB, REDREDFYELB1, REDREDFYELB2
     COMMON SHARED XS5, XS4, XS3, XS2, XS1
REM** GLOBALIZE TIMER VARIABLES
     COMMON SHARED Start!, Finish!, Report$, Diagnose$, Signal$
     COMMON SHARED Hours, Mins, Seconds!, Ratio, StartFC!, FinishFC!, T1SAVE&
     COMMON SHARED VERSION$
     VERSION$ = "V 2021-10-11"
     

REM** DIMENSION RAILROAD DEVICES
     DIM SHARED CTCSWL(30), CTCSGLN(30), CTCSGLS(30), CTCPB(30), CTCLEDSW(30), CTCLEDSIG(30), SM(150), SMFBN(150), SMFBR(150), BLK(175), SMFBT(20), SIGR(68), SIGL(68)
     DIM SHARED SM$(180), SMFB$(180), CTCSWL$(30), CTCLEDSW$(30), CTCSIGL$(30), CTCLEDSIG$(30), CTCPB$(30), BLK$(170), SIGN$(30), SIGS$(30), SIGR$(68), SIGL$(68), CrossBuck(10), Bell(10)
     DIM SHARED PB(50), LED(250), SWITCHN(150), SWITCHREV(150), KEYSWITCH(150), INHAND(150), NHAND(150), Light(150), TD(150), UL(150), TRACKNORTH(10), TRACKSOUTH(10)
     
     REM**INITIALIZE CONSTANTS FOR PACKING AND UNPACKING I/O BYTES
     B0 = 1: B1 = 2: B2 = 4: B3 = 8: B4 = 16: B5 = 32: B6 = 64: B7 = 128
     W1 = 1: W2 = 3: W3 = 7: W4 = 15: W5 = 31: W6 = 63: W7 = 127

  REM**DEFINE PUSHBUTTON AND TOGGLE CONSTANTS
        OCC = 1: REM BLOCK OCCUPIED
        CLR = 0: REM BLOCK CLEAR
        PBP = 1: REM push button pressed 1
  REM**DEFINE TURNOUT POSITIONS
        TUN = 1'TURNOUT NORMAL   01
        TUR = 2'TURNOUT REVERSED 10
  REM**DEFINE CTC SIG LEVER DIRECTION POSITION
        NORTH = 4: 'RIGHT
        SOUTH = 1: 'LEFT
        
  REM ** DEFINE LED PANEL ASPECTS
        GRN = 1: ' LED is green + / binary = 01
        RED = 2: ' LED is red - / binary = 10
        YEL = 3: ' LED is yellow (ac) / binary = 11
        REDRED = 10: 'LED is red over red /binary 1010
        REDGRN = 9: ' LED is red over greenbinary 1001
        GRNRED = 6: ' LED is green over red / binary 0110
        REDYEL = 11: ' LED is red over yellow / binary 1011
        YELRED = 14: ' LED is yellow over red / binary 1110

  REM ** DEFINE BLMA type SIGNAL ASPECTS
        DRK = 0: ' signal is dark- aproach lit / binary = 000000
        REDB = 4: ' binary 100
        YELB = 2: ' binary 010
        GRNB = 1: ' binary 001
        REDREDB = 36: ' signal is red over red / binary = 100100
        REDYELB = 34: ' signal is red over yellow / binary = 100010
        YELREDB = 20: ' signal is yellow over red / binary 010100
        REDGRNB = 33: ' signal is red over green / binary = 100001
        GRNREDB = 12: ' signal is green over red / binary = 001100
        'REDDRK = 32: ' signal is red over flashing red / binary 100100/100000
        REDREDREDB = 164: ' signal is red over red over red / binary = 10100100
        GRNREDREDB = 161: ' signal is green over red over red / binary = 10100001
        YELREDREDB = 162: ' signal is yellow over red over red / binary = 10100010
        REDYELREDB = 148: ' signal is red over yel over red / binary = 10010100
        REDGRNREDB = 140: ' signal is red over green over red / binary = 10001100
        REDREDYELB = 100: ' signal is red over red over yellow / binary 01100100

CALL INITRR: REM**INITALIZE I/O DEVICES

CALL CTCBOARD

SUB ABSIGNALS

'********************* LEFT *** SOUTHBOUND *******************************
SIG18L: ' Campbellsburg S Tall & Dwarf
        SIGL(18) = REDB: SIGL(17) = REDB
        IF BLK(83) + BLK(84) > 0 GOTO SIG20L
        IF SMFBN(17) = TUN THEN
           IF SIGL(16) <> REDREDB THEN SIGL(18) = GRNB ELSE SIGL(18) = YELB
        ELSE
           IF SIGL(19) <> REDREDB THEN SIGL(17) = GRNB ELSE SIGL(17) = YELB
        END IF

SIG20L: ' Campbellsburg dwarf
        SIGL(20) = REDB: SIGL(41) = REDB
        IF BLK(79) + BLK(82) > 0 GOTO SIG22L
        IF SMFBN(19) = TUN THEN
           SIGL(20) = REDB
        ELSE
           IF SIGL(18) <> REDB THEN SIGL(20) = GRNB ELSE SIGL(20) = YELB
        END IF

SIG22L: ' Campbellsburg dwarf
        SIGL(22) = REDB
        IF BLK(80) + BLK(81) > 0 GOTO SIG24L
        IF SMFBN(21) = TUN THEN
           SIGL(22) = REDB
        ELSE
           IF SIGL(17) <> REDB THEN SIGL(22) = GRNB ELSE SIGL(20) = YELB
        END IF

SIG24L: ' Campbellsburg crossover double head
        SIGL(24) = REDREDB
        IF SMFBN(19) <> TUN THEN GOTO SIG28L
        IF SMFBN(23) = TUN THEN
          IF BLK(78) + BLK(79) + BLK(82) <> 0 THEN GOTO SIG28L
          IF SIGL(18) <> REDB THEN SIGL(24) = GRNREDB ELSE SIGL(24) = YELREDB
        ELSE
          IF BLK(78) + BLK(80) + BLK(81) <> 0 THEN GOTO SIG28L
          IF SIGL(18) <> REDRED THEN SIGL(24) = REDGRNB ELSE SIGL(24) = REDYELB
        END IF

SIG28L: ' N Campbellsburg Tripple Head
        SIGL(28) = REDREDREDB
        IF SMFBN(27) = TUN THEN
         IF SMFBN(25) = TUN THEN
          IF BLK(74) + BLK(75) + BLK(77) <> 0 THEN GOTO SIG29L
            IF SIGL(24) <> REDREDB THEN SIGL(28) = GRNREDREDB ELSE SIGL(28) = YELREDREDB
         ELSE
            IF BLK(74) + BLK(75) + BLK(77) <> 0 THEN GOTO SIG29L
            IF SIGL(22) <> REDB THEN SIGL(28) = REDREDFYELB ELSE SIGL(28) = REDREDYELB
            ' logic to add flashing yellow, greem not available
         END IF
        ELSE
          IF BLK(74) + BLK(76) <> 0 THEN GOTO SIG29L
          IF SIGL(20) <> REDB THEN SIGL(28) = REDGRNREDB ELSE SIGL(28) = REDYELREDB
        END IF

SIG29L: ' DWARF PROTECTING CRR
       SIGL(29) = REDB
        IF SMFBN(31) = TUN THEN
         IF BLK(57) + BLK(60) + BLK(64) + BLK(65) + BLK(67) > 0 GOTO SIG30L
         SIGL(29) = GRNB
        ELSE
         SIGL(29) = REDB
        END IF

SIG30L: ' S Worthville SIGL(30) DOUBLE HEAD

       SIGL(30) = REDREDB
       IF BLK(59) > 0 GOTO SIG31L
       IF SMFBN(31) = TUN THEN
         IF SMFBN(29) = TUN THEN
           IF BLK(59) + BLK(62) + BLK(63) + BLK(73) > 0 GOTO SIG31L
           IF SIGL(28) <> REDREDREDB THEN SIGL(30) = GRNREDB ELSE SIGL(30) = YELREDB
         ELSE
           SIGL(30) = REDREDB
         END IF
       ELSE
         IF BLK(59) + BLK(60) + BLK(64) + BLK(65) + BLK(67) > 0 GOTO SIG31L
         SIGL(30) = REDGRNB
       END IF

SIG31L:  ' DWARF
       SIGL(31) = REDB
       IF BLK(61) + BLK(62) + BLK(63) + BLK(73) + BLK(74) > 0 GOTO SIG32L
       IF SMFBN(29) = TUN THEN GOTO SIG32L
       IF SIGL(28) <> REDREDREDB THEN SIGL(31) = GRNB ELSE SIGL(31) = YELB

SIG32L:
      ' N Worthville signal bridge main (center track) 10/31/2018
        SIGL(32) = REDRED
        IF SMFBN(33) = TUN THEN
          IF BLK(55) + BLK(58) <> 0 THEN GOTO SIG34L
          IF SIGL(30) = (YELB OR GRNB) THEN SIGL(32) = GRNRED ELSE SIGL(32) = YELRED
        ELSE
          SIGL(32) = REDRED
        END IF

SIG34L:
      ' N Worthville signal bridge siding (left track) 10/31/2018
        SIGL(34) = REDRED
        IF SMFBN(33) = TUN THEN
          IF BLK(53) + BLK(54) <> 0 THEN GOTO SIG36L
          IF SIGL(31) = (YELB OR GRNB) THEN SIGL(34) = GRNRED ELSE SIGL(34) = YELRED
        ELSE
          IF BLK(53) + BLK(58) + BLK(55) <> 0 THEN GOTO SIG36L
          IF SIGL(30) <> (REDB OR FREDB) THEN SIGL(34) = REDGRN ELSE SIGL(34) = REDYEL
        END IF

SIG36L:
        '18-MAY 2021
        SIGL(36) = REDREDB
        IF SMFBN(35) = TUN THEN
          IF BLK(52) <> 0 THEN GOTO SIG38L
          IF SIGL(32) <> REDRED THEN SIGL(36) = GRNREDB ELSE SIGL(36) = YELREDB
        ELSE
          IF BLK(52) + BLK(56) <> 0 THEN GOTO SIG38L
          IF SIGL(29) <> REDB THEN SIGL(36) = REDGRNB ELSE SIGL(36) = REDYELB
        END IF

SIG38L: ' N Worthville double head signal
        SIGL(38) = REDREDB
        IF SMFBN(37) = TUN THEN
          IF BLK(49) + BLK(50) + BLK(52) <> 0 THEN GOTO CROSSBUCK5
          IF SIGL(32) <> REDRED THEN SIGL(38) = GRNREDB ELSE SIGL(38) = YELREDB
        ELSE
          IF BLK(49) + BLK(51) <> 0 THEN GOTO CROSSBUCK5
          IF SIGL(34) <> REDRED THEN SIGL(38) = REDGRNB ELSE SIGL(38) = REDYELB
        END IF

'*************************** Grade Crossing Protection S Worthville *****************
CROSSBUCK5:
REM at this grade crossing there are five tracks and two crossovers
' this creates several route possibilities. Each route is monitored seperatly.

' set flashing crossbuck and bell to off before calculating state again
 CrossBuck(5) = DRK
 Bell(5) = 0

IF SM(29) = TUR THEN
 X1 = BLK(61)
 SXA1 = BLK(62) + BLK(63)
 NXA1 = BLK(53) + BLK(54)
 TD1 = TD(101)
 CALL SGCCS(NXA1, SXA1, X1, XS1, TD1, PGCC1)
 TD(101) = TD1
 IF PGCC1 = 1 THEN CrossBuck(5) = FREDGRN: Bell(5) = 1
'LOCATE 4, 5: PRINT "XA1 "; : PRINT XA; : PRINT " North aproach "; : PRINT NXA1; : PRINT " SOUTH Approach "; : PRINT SXA1; : PRINT "Island "; : PRINT X1; : PRINT " Stick "; : PRINT XS1; : PRINT " PGCC1 "; : PRINT PGCC1

ELSE
 IF SM(31) = TUN THEN
  X2 = BLK(59)
  SXA2 = BLK(62) + BLK(63)
  NXA2 = BLK(55) + BLK(58)
  TD2 = TD(102)
  CALL SGCCS(NXA2, SXA2, X2, XS2, TD2, PGCC2)
  TD(102) = TD2
  IF PGCC2 = 1 THEN CrossBuck(5) = FREDGRN: Bell(5) = 1
'  LOCATE 5, 5: PRINT "XA2 "; : PRINT XA; : PRINT " North aproach "; : PRINT NXA2; : PRINT " SOUTH Approach "; : PRINT SXA2; : PRINT "Island "; : PRINT X2; : PRINT " Stick "; : PRINT XS2; : PRINT " PGCC2 "; : PRINT PGCC2
 END IF
END IF

IF SM(31) = TUN THEN
  X2 = BLK(59)
  SXA2 = BLK(62) + BLK(63)
  NXA2 = BLK(55) + BLK(58)
  TD2 = TD(102)
  CALL SGCCS(NXA2, SXA2, X2, XS2, TD2, PGCC2)
  TD(102) = TD2
  IF PGCC2 = 1 THEN CrossBuck(5) = FREDGRN: Bell(5) = 1
'  LOCATE 5, 5: PRINT "XA2 "; : PRINT XA; : PRINT " North aproach "; : PRINT NXA2; : PRINT " SOUTH Approach "; : PRINT SXA2; : PRINT "Island "; : PRINT X2; : PRINT " Stick "; : PRINT XS2; : PRINT " PGCC2 "; : PRINT PGCC2

  X4 = BLK(57)
  SXA4 = BLK(60) + BLK(67)
  NXA4 = BLK(56)
  TD4 = TD(104)
  CALL SGCCS(NXA4, SXA4, X4, XS4, TD4, PGCC4)
  IF PGCC4 = 1 THEN CrossBuck(5) = FREDGRN: Bell(5) = 1
  TD(104) = TD4
'  LOCATE 7, 10: PRINT "XA4 "; : PRINT XA4; : PRINT " North aproach "; : PRINT NXA4; : PRINT " SOUTH Approach "; : PRINT SXA4; : PRINT "Island "; : PRINT X4; : PRINT " Stick "; : PRINT XS4; : PRINT " PGCC4 "; : PRINT PGCC4
'  LOCATE 7, 1: PRINT "TD4 "; : PRINT TD4; : PRINT "TD(104) "; : PRINT TD(104)
ELSE
  X3 = BLK(59)
  SXA3 = BLK(60) + BLK(67)
  NXA3 = BLK(55) + BLK(58)
  TD3 = TD(103)
  CALL SGCCS(NXA3, SXA3, X3, XS3, TD3, PGCC3)
  IF PGCC3 = 1 THEN CrossBuck(5) = FREDGRN: Bell(5) = 1
  TD(103) = TD3
'  LOCATE 6, 5: PRINT "XA3 "; : PRINT XA; : PRINT " North aproach "; : PRINT NXA; : PRINT " SOUTH Approach "; : PRINT SXA; : PRINT "Island "; : PRINT X; : PRINT " Stick "; : PRINT XS; : PRINT " PGCC3 "; : PRINT PGCC3
'   LOCATE 6, 1: PRINT "TD3 "; : PRINT TD(103)
END IF

IF BLK(66) = 1 THEN CrossBuck(5) = FREDGRN: Bell(5) = 1

SIG40L:
       ' S Sparta signal & dwarf
        SIGL(40) = REDB: SIGL(41) = REDB
        IF BLK(44) + BLK(45) > 0 GOTO SIG42L
        IF SMFBN(39) = TUN THEN
           IF SIGL(38) <> REDREDB THEN SIGL(40) = GRNB ELSE SIGL(40) = YELB
        ELSE
           IF SIGL(38) <> REDREDB THEN SIGL(41) = GRNB ELSE SIGL(41) = YELB
        END IF

SIG42L: ' dwarf west (passenger) siding
        SIGL(42) = REDB
        IF BLK(42) + BLK(43) > 0 GOTO SIG46L
        IF SMFBN(41) = TUN THEN
           GOTO SIG46L
         ELSE
           IF SIGL(40) <> REDB THEN SIGL(42) = GRNB ELSE SIGL(42) = YELB
        END IF


SIG46L: ' TRIPLE HEAD N Sparta
        SIGL(46) = REDREDREDB
        IF SMFBN(45) = TUN THEN
         IF SMFBN(43) = TUN THEN
          IF BLK(37) + BLK(38) + BLK(39) + BLK(42) + BLK(43) <> 0 THEN GOTO SIG48L
          IF SMFBN(41) <> 1 THEN GOTO SIG48L
            IF SIGL(40) <> REDB THEN SIGL(46) = GRNREDREDB ELSE SIGL(46) = YELREDREDB
         
         ELSE
            IF BLK(37) + BLK(38) + BLK(41) <> 0 THEN GOTO SIG48L
            IF SIGL(41) <> REDB THEN SIGL(46) = REDREDFYELB ELSE SIGL(46) = REDREDYELB
            ' logic to add flashing yellow, greem not available
         END IF

        ELSE
          IF BLK(37) + BLK(40) <> 0 THEN GOTO SIG48L
          IF SIGL(42) <> REDB THEN SIGL(46) = REDGRNREDB ELSE SIGL(46) = REDYELREDB
        END IF

SIG48L:
        ' S Walton

        SIGL(48) = REDB: SIGL(49) = REDB
        IF BLK(32) + BLK(33) > 0 GOTO SIG54L
        IF SMFBN(49) <> TUN GOTO SIG54L
        IF SMFBN(47) = TUN THEN
           IF SIGL(46) <> REDREDREDB THEN SIGL(48) = GRNB ELSE SIGL(48) = YELB
        ELSE
           IF SIGL(46) <> REDREDREDB THEN SIGL(49) = GRNB ELSE SIGL(49) = YELB
        END IF


SIG54L:
        ' N Walton double head

        SIGL(54) = REDREDB
        IF SMFBN(53) = TUN THEN
          IF BLK(26) + BLK(29) + BLK(32) <> 0 THEN GOTO SIG55L
          IF SIGL(48) <> REDB THEN SIGL(54) = GRNREDB ELSE SIGL(54) = YELREDB
        ELSE
          IF BLK(26) + BLK(28) <> 0 THEN GOTO SIG55L
          IF SIGL(49) <> REDB THEN SIGL(54) = REDGRNB ELSE SIGL(54) = REDYELB
        END IF

        'LATONIA

SIG55L: ' Dwarf at S yard
        SIGL(55) = REDB
        IF BLK(24) + BLK(25) + BLK(27) > 0 GOTO SIG56L
        IF SMFBN(57) + SMFBN(55) = 0 THEN
           IF SIGL(54) <> REDREDB THEN SIGL(55) = GRNB ELSE SIGL(55) = YELB
        ELSE
           SIGL(55) = REDB
        END IF

SIG56L: ' Tall single S yard
        SIGL(56) = REDB
        IF BLK(24) + BLK(25) + BLK(27) > 0 GOTO SIG57L
        IF SMFBN(57) = 1 AND SMFBN(55) = 0 THEN
           IF SIGL(54) <> REDREDB THEN SIGL(56) = GRNB ELSE SIGL(56) = YELB
        ELSE
           SIGL(56) = REDB
        END IF

SIG57L: ' dwarf N main
        SIGL(57) = REDB
        IF BLK(25) + BLK(27) > 0 GOTO SIG58L
        IF SMFBN(55) = 1 THEN
           IF SIGL(54) <> REDREDB THEN SIGL(57) = GRNB ELSE SIGL(57) = YELB
        ELSE
           SIGL(57) = REDB
        END IF

SIG58L: ' Latonia crossover double head
        SIGL(58) = REDREDB
        IF SMFBN(59) = TUN THEN
          IF BLK(21) + BLK(22) <> 0 THEN GOTO SIG60L
          IF SIGL(57) <> REDB THEN SIGL(58) = GRNREDB ELSE SIGL(58) = YELREDB
        ELSE
          IF BLK(20) + BLK(21) + BLK(23) <> 0 THEN GOTO SIG60L
          IF SIGL(56) <> REDB THEN SIGL(58) = REDGRNB ELSE SIGL(58) = REDYELB
        END IF

SIG60L: ' Latonia crossover dwarf
        SIGL(60) = REDB
        IF (BLK(20) + BLK(23)) > 0 GOTO SIG62L
        IF SMFBN(59) = TUN THEN
           IF SIGL(56) <> REDB THEN SIGL(60) = GRNB ELSE SIGL(60) = YELB
        ELSE
           SIGL(60) = REDB
        END IF

SIG62L:  ' DOUBLE HEAD N LATONIA
        SIGL(62) = REDREDB
        IF SMFBN(65) = TUN THEN
          IF BLK(169) + BLK(170) + BLK(20) <> 0 THEN GOTO SIG64L
          IF SIGL(60) <> REDB THEN SIGL(62) = GRNREDB ELSE SIGL(62) = YELREDB
        ELSE
          IF BLK(170) <> 0 THEN GOTO SIG64L
          SIGL(62) = REDYELB
        END IF

SIG64L:

'********************* RIGHT *** NORTHBOUND *******************************
SIG65R: ' DeCoursey crossover single head 1/28/21
         LOCATE 12, 1
         SIGR(65) = REDB
         IF SMFBN(67) = TUN THEN
           IF (BLK(16) + BLK(13)) > 0 GOTO SIG64R
           SIGR(65) = YELB
         END IF

SIG64R: 'DeCoursey crossover double(64) head 1/28/21
         SIGR(64) = REDREDB
         IF SMFBN(67) = TUN THEN
           IF (BLK(15) + BLK(14)) > 0 GOTO SIG62R
           SIGR(64) = YELREDB
         ELSE
           IF (BLK(15) + BLK(16) + BLK(13)) > 0 GOTO SIG62R
           SIGR(64) = REDYELB
         END IF

SIG62R: 'N LATONIA
        SIGR(62) = REDB: SIGR(63) = REDB
        IF BLK(170) + BLK(18) > 0 GOTO SIG61R
        IF SMFBN(65) = TUN THEN
           IF SIGR(65) <> REDB THEN SIGR(62) = GRNB ELSE SIGR(62) = YELB
        ELSE
           IF SIGR(65) <> REDB THEN SIGR(63) = GRNB ELSE SIGR(63) = YELB
        END IF

SIG61R: ' Yard Shortcut
        SIGR(61) = REDB
        IF BLK(169) > 0 GOTO SIG60R
         IF SMFBN(63) <> TUN THEN
           IF SIGR(62) <> REDB THEN SIGR(61) = GRNB ELSE SIGR(61) = YELB
         ELSE
           GOTO SIG60R
         END IF

SIG60R: ' Latonia crossover double head
        SIGR(60) = REDREDB
        IF SMFBN(59) = TUN THEN
          IF (BLK(20) + BLK(169)) > 0 THEN GOTO SIG58R
          IF SMFBN(63) <> TUN THEN GOTO SIG58R
          IF SIGR(62) <> REDB THEN SIGR(60) = GRNREDB ELSE SIGR(60) = YELREDB
        ELSE
          IF (BLK(20) = OCC) OR (BLK(21) = OCC) OR (BLK(168) = OCC) OR (BLK(19) = OCC) THEN GOTO SIG58R
          IF SIGR(64) <> REDREDB THEN SIGR(60) = REDGRNB ELSE SIGR(60) = REDYELB
        END IF

SIG58R: ' S Latonia  crossover
        SIGR(58) = REDB
        IF BLK(21) + BLK(19) + BLK(70) > 0 GOTO SIG56R
        IF SMFBN(59) = TUN THEN
           IF SIGR(64) <> REDREDB THEN SIGR(58) = GRNB ELSE SIGR(58) = YELB
        END IF
                          

SIG56R: ' TRIPLE HEAD S LATONIA
        IF SMFBN(55) = 1 THEN LED(55) = TUN ELSE LED(55) = TUR: ' for control panel Latonia
        SIGR(56) = REDREDREDB
        IF SMFBN(55) = TUN THEN
          IF BLK(25) + BLK(22) + BLK(21) <> 0 THEN GOTO SIG54R
          IF SIGR(58) <> REDB THEN SIGR(56) = GRNREDREDB ELSE SIGR(56) = YELREDREDB
        ELSE
          'IF BLK(24) + BLK(25) <> 0 THEN GOTO SIG54R
           IF SMFBN(57) = TUN THEN
            IF BLK(25) + BLK(24) + BLK(23) + BLK(20) <> 0 THEN GOTO SIG54R
            IF SIGR(60) <> REDREDB THEN SIGR(56) = REDGRNREDB ELSE SIGR(56) = REDYELREDB
           ELSE
            IF BLK(24) + BLK(25) <> 0 THEN GOTO SIG54R
            SIGR(56) = REDREDYELB
           END IF
        END IF


SIG54R:
        ' N Walton

        SIGR(54) = REDB: SIGR(55) = REDB
        IF BLK(26) + BLK(27) > 0 GOTO SIG48R
        IF SMFBN(53) = TUN THEN
           IF SIGR(56) <> REDREDREDB THEN SIGR(54) = GRNB ELSE SIGR(54) = YELB
        ELSE
           IF SIGR(56) <> REDREDREDB THEN SIGR(55) = GRNB ELSE SIGR(55) = YELB
        END IF


SIG48R: ' S Walton double head

        SIGR(48) = REDREDB
        IF SMFBN(47) = TUN THEN
          IF SMFBN(49) = TUN THEN
           IF BLK(29) + BLK(30) + BLK(32) <> 0 THEN GOTO SIG46R
           IF SMFBN(47) <> TUN THEN GOTO SIG46R: ' THIS LINE DOES NOT SEEM TO WORK
           IF SIGR(54) <> REDB THEN SIGR(48) = GRNREDB ELSE SIGR(48) = YELREDB
          ELSE
           IF BLK(32) = OCC THEN SIGR(48) = REDREDB: GOTO SIG46R
           IF BLK(31) = OCC THEN SIGR(48) = FREDB + 32 ELSE SIGR(48) = REDYELB
          END IF
        ELSE
          IF BLK(28) + BLK(32) <> 0 THEN GOTO SIG46R
          IF SIGR(55) <> REDB THEN SIGR(48) = REDGRNB ELSE SIGR(48) = REDYELB
        END IF



SIG46R: ' N Sparta single head & 2 dwarfs  11-20-2020

        SIGR(42) = REDB: SIGR(46) = REDB: SIGR(44) = REDB
        IF BLK(37) + BLK(33) > 0 GOTO SIG40R
        IF SMFBN(45) = TUN THEN
          IF SMFBN(43) = TUN THEN
           IF BLK(38) > 0 THEN GOTO SIG40R
           IF SIGR(48) <> REDREDB THEN SIGR(46) = GRNB ELSE SIGR(46) = YELB
          ELSE
           IF BLK(38) > 0 THEN GOTO SIG40R
           IF SIGR(48) <> REDREDB THEN SIGR(44) = GRNB ELSE SIGR(44) = YELB
          END IF
        ELSE
          IF SIGR(48) <> REDREDB THEN SIGR(42) = GRNB ELSE SIGR(42) = YELB
        END IF
        
SIG40R: ' S Sparta triple head  12-17-2019
        SIGR(40) = REDREDREDB
        IF SMFBN(39) = TUN THEN
          IF SMFBN(41) = TUN THEN
            IF BLK(37) + BLK(38) + BLK(39) + BLK(42) + BLK(43) + BLK(44) <> 0 THEN GOTO SIG38R
            IF SIGR(46) <> REDB THEN SIGR(40) = GRNREDREDB ELSE SIGR(40) = YELREDREDB
          ELSE
            IF BLK(37) + BLK(40) + BLK(42) + BLK(43) + BLK(44) <> 0 THEN GOTO SIG38R
            IF SIGR(42) <> REDB THEN SIGR(40) = REDREDFYELB ELSE SIGR(40) = REDREDYELB
             ' logic to add flashing yellow, greem not available
          END IF
        ELSE
          IF BLK(41) + BLK(44) <> 0 THEN GOTO SIG38R
          IF SIGR(45) <> REDB THEN SIGR(40) = REDGRNREDB ELSE SIGR(40) = REDYELREDB
        END IF

SIG38R: ' N Worthville tall & dwarf
        SIGR(38) = REDB: SIGR(39) = REDB
        IF BLK(45) + BLK(49) > 0 GOTO SIG36R
        IF SMFBN(37) = TUN THEN
           IF SIGR(40) <> REDREDREDB THEN SIGR(38) = GRNB ELSE SIGR(38) = YELB
        ELSE
           IF SIGR(40) <> REDREDREDB THEN SIGR(39) = GRNB ELSE SIGR(39) = YELB
        END IF

SIG36R:   ' Worthville dwarf W (coal) siding
        SIGR(36) = REDB
        IF BLK(52) + BLK(50) + BLK(49) > 0 THEN GOTO SIG34R
        IF SMFBN(35) = TUN THEN
           GOTO SIG34R
        ELSE
           IF SIGR(38) <> REDB THEN SIGR(36) = GRNB ELSE SIGR(36) = YELB
        END IF

SIG34R:
        ' Worthville Dwarf Siding
        SIGR(34) = REDB
        IF BLK(53) + BLK(51) > 0 THEN GOTO SIG32R
        IF SMFBN(33) = TUN THEN
         IF SIGR(39) = REDB THEN SIGR(34) = YELB ELSE SIGR(34) = GRNB
        ELSE
          SIGR(34) = REDB
        END IF

SIG32R:
        ' Worthville double head 21-June-2019
        SIGR(32) = REDREDB

        IF SMFBN(33) = TUN THEN
          IF SMFBN(35) = TUN THEN
           IF BLK(58) + BLK(52) + BLK(50) <> 0 THEN GOTO SIG30R
           IF SIGR(38) <> REDB THEN SIGR(32) = GRNREDB ELSE SIGR(32) = YELREDB
          ELSE
                SIGR(32) = REDREDB: GOTO SIG30R
          END IF
        ELSE
          IF BLK(58) + BLK(53) + BLK(51) <> 0 THEN GOTO SIG30R
          IF SIGR(39) <> REDB THEN SIGR(32) = REDGRNB ELSE SIGR(32) = REDYELB
        END IF


SIG30R: 'S Worthville double head 21-June-2019

        SIGR(30) = REDREDB
        IF SMFBN(29) = TUN THEN
          IF SMFBN(31) = TUN THEN
           IF BLK(62) + BLK(59) + BLK(55) <> 0 THEN GOTO SIG28R
           IF SIGR(32) <> REDREDB THEN SIGR(30) = GRNREDB ELSE SIGR(30) = YELREDB
          ELSE
           SIGR(30) = REDREDB: GOTO SIG28R
          END IF
        ELSE
          IF BLK(62) + BLK(61) + BLK(54) <> 0 THEN GOTO SIG28R
          IF SIGR(34) <> REDB THEN SIGR(30) = REDGRNB ELSE SIGR(30) = REDYELB
        END IF


SIG28R:
SIG10R:
        ' Worthville Dwarf CRR must be renumbered to SIG30R when others renumbered
        SIGR(10) = REDB
        IF SMFBN(31) = TUN THEN
         IF BLK(67) + BLK(60) + BLK(56) > 0 THEN GOTO SIG8R
         IF SIGR(36) <> REDB THEN SIGR(10) = GRNB ELSE SIGR(10) = YELB
        ELSE
         IF BLK(67) + BLK(60) + BLK(59) + BLK(55) > 0 THEN GOTO SIG8R
         IF SIGR(32) <> REDREDB THEN SIGR(10) = GRNB ELSE SIGR(10) = YELB
        END IF

SIG8R:
IF Signal$ = "N" GOTO 777
'************************ APROACH LIGHTING *************************
        IF BLK(74) + BLK(73) + BLK(67) + BLK(64) + BLK(63) + BLK(62) + BLK(61) + BLK(60) + BLK(59) = 0 THEN SIGR(30) = DRK: SIGR(10) = DRK
        IF BLK(51) + BLK(52) + BLK(53) + BLK(54) + BLK(55) + BLK(56) + BLK(57) + BLK(58) + BLK(59) + BLK(61) + BLK(62) = 0 THEN SIGL(30) = DRK: SIGL(31) = DRK: SIGL(29) = DRK
        IF BLK(45) + BLK(49) + BLK(50) + BLK(51) + BLK(52) + BLK(53) + BLK(56) + BLK(58) = 0 THEN SIGL(32) = DRK: SIGL(34) = DRK: SIGL(36) = DRK
        IF BLK(53) + BLK(54) + BLK(55) + BLK(56) + BLK(58) + BLK(59) + BLK(60) + BLK(61) + BLK(62) + BLK(63) + BLK(64) + BLK(67) = 0 THEN SIGR(32) = DRK: SIGR(34) = DRK: SIGR(36) = DRK
        IF BLK(49) + BLK(50) + BLK(51) + BLK(52) + BLK(53) + BLK(54) + BLK(55) + BLK(58) + BLK(60) = 0 THEN SIGR(38) = DRK: SIGR(39) = DRK
        
        IF BLK(44) + BLK(45) + BLK(49) = 0 THEN SIGL(38) = DRK
        IF BLK(37) + BLK(38) + BLK(39) + BLK(40) + BLK(41) + BLK(42) + BLK(43) + BLK(44) + BLK(45) = 0 THEN SIGL(40) = DRK: SIGL(41) = DRK: SIGL(42) = DRK
        IF BLK(37) + BLK(38) + BLK(39) + BLK(40) + BLK(41) + BLK(42) + BLK(43) + BLK(44) = 0 THEN SIGR(42) = DRK: SIGR(44) = DRK: SIGR(46) = DRK
        IF BLK(33) + BLK(37) = 0 THEN SIGL(46) = DRK
        IF BLK(28) + BLK(29) + BLK(32) = 0 THEN SIGL(48) = DRK: SIGL(49) = DRK
        IF BLK(44) + BLK(45) = 0 THEN SIGR(40) = DRK
        IF BLK(33) + BLK(32) = 0 THEN SIGR(48) = DRK
        IF BLK(26) + BLK(27) = 0 THEN SIGL(54) = DRK
        IF BLK(26) + BLK(29) + BLK(28) = 0 THEN SIGR(54) = DRK: SIGR(55) = DRK
        IF BLK(27) + BLK(26) + BLK(25) + BLK(24) = 0 THEN SIGR(56) = DRK
        IF BLK(169) + BLK(170) + BLK(19) + BLK(20) + BLK(21) + BLK(22) + BLK(23) + BLK(24) + BLK(25) = 0 THEN SIGL(56) = DRK: SIGL(57) = DRK
        IF BLK(20) + BLK(21) + BLK(22) + BLK(23) + BLK(24) + BLK(25) + BLK(27) = 0 THEN SIGR(58) = DRK: SIGR(60) = DRK
        IF BLK(18) + BLK(19) + BLK(20) + BLK(21) + BLK(169) + BLK(170) = 0 THEN SIGL(58) = DRK: SIGL(60) = DRK
        IF BLK(19) + BLK(169) + BLK(170) = 0 AND SMFBN(65) = 1 THEN SIGR(62) = DRK: SIGR(63) = DRK
        IF BLK(15) + BLK(16) + BLK(18) + BLK(19) + BLK(170) = 0 THEN SIGL(62) = DRK
777

END SUB

SUB CRTDISPLAY

REM**DISPLAY RAILROAD STATUS ON MONITOR SCREEN

'LOCATE 1, 1: PRINT T$ ' real time from computer clock
'LOCATE 3, 1: PRINT "Start Time "; : PRINT USING "######"; Start
'LOCATE 2, 1: PRINT "Finish Time"; : PRINT USING "######"; Finish
'LOCATE 4, 1: PRINT "Lapst Time "; : PRINT USING "######"; LapsTime!
'LOCATE 5, 1: PRINT "Fast Time  "; : PRINT USING "######"; FastClock!
LOCATE 1, 73: PRINT USING "##"; Hours; : PRINT ":"; : PRINT USING "##"; Mins
LOCATE 1, 78: PRINT ":"; : PRINT USING "##"; Seconds!
'LOCATE 2, 70: PRINT Hour$; : PRINT ":"; : PRINT Min$; : PRINT ":"; : PRINT Sec$
'LOCATE 6, 1: PRINT "Time of Day"; : PRINT TimeOfDay
'LOCATE 7, 1: PRINT "Street Lights"; : PRINT StreetLights
'LOCATE 8, 1: PRINT "Control Tower"; : PRINT ControlTower



'Start! = TIMER

IF Finish! - Start! <= 15 THEN GOTO DeCoursey
IF Finish! - Start! <= 16 AND Finish! - Start! > 15 THEN GOTO Latonia
IF Finish! - Start! <= 17 AND Finish! - Start! > 16 THEN GOTO Walton
IF Finish! - Start! <= 30 AND Finish! - Start! > 17 THEN GOTO Sparta
IF Finish! - Start! <= 31 AND Finish! - Start! > 30 THEN GOTO Worthville
IF Finish! - Start! <= 45 AND Finish! - Start! > 31 THEN GOTO Campbellsburg
IF Finish! - Start! <= 46 AND Finish! - Start! > 45 THEN GOTO CTCmach
IF Finish! - Start! > 46 THEN Start! = TIMER: GOTO LastReport


DeCoursey:
IF Report$ <> "DeCoursey" THEN CLS : CALL HEADER: Report$ = "DeCoursey"

LOCATE 5, 17: PRINT "DeCoursey Yard"
FOR I = 1 TO 17
 IF BLK(I) = 1 THEN
  CLOR(I) = 4
 ELSE
  CLOR(I) = 7
 END IF
NEXT I

FOR I = 171 TO 173
 IF BLK(I) = 1 THEN
  CLOR(I) = 4
 ELSE
  CLOR(I) = 7
 END IF
NEXT I

LOCATE 7, 1: COLOR CLOR(1), 0: PRINT "South Main to CRR   "
LOCATE 8, 1: COLOR CLOR(171), 0: PRINT "SW #71 Interlock     "
LOCATE 9, 1: COLOR CLOR(2), 0: PRINT "South Yard Throat   "
LOCATE 10, 1: COLOR CLOR(3), 0: PRINT "Bypass Track        "
LOCATE 11, 1: COLOR CLOR(4), 0: PRINT "Yard Track #1       "
LOCATE 12, 1: COLOR CLOR(5), 0: PRINT "Yard Track #2       "
LOCATE 13, 1: COLOR CLOR(6), 0: PRINT "Yard Track #3       "
LOCATE 14, 1: COLOR CLOR(7), 0: PRINT "Yard Track #4       "
LOCATE 15, 1: COLOR CLOR(8), 0: PRINT "Yard Track #5       "
LOCATE 16, 1: COLOR CLOR(9), 0: PRINT "Yard Track #6       "
LOCATE 17, 1: COLOR CLOR(10), 0: PRINT "Yard Track #7       "
LOCATE 18, 1: COLOR CLOR(11), 0: PRINT "North Yard Throat   "

LOCATE 7, 35: COLOR CLOR(173), 0: PRINT "SW #69 X/O Main N   "
LOCATE 8, 35: COLOR CLOR(15), 0: PRINT "SW #69 X/O Main S   "
LOCATE 9, 35: COLOR CLOR(13), 0: PRINT "North Left Hand Main"
LOCATE 10, 35: COLOR CLOR(14), 0: PRINT "North Right Hand Main"
LOCATE 11, 35: COLOR CLOR(17), 0: PRINT "SW #67 X/O Main N    "
LOCATE 12, 35: COLOR CLOR(16), 0: PRINT "SW #67 X/O Main S    "

FOR I = 67 TO 71 STEP 2
 IF SMFBN(I) = 1 THEN
  SMFB$(I) = "N":
  CLOR(I) = 7
 ELSE
  SMFB$(I) = "R":
  CLOR(I) = 4
 END IF
NEXT I

LOCATE 8, 20: COLOR CLOR(71), 0: PRINT SMFB$(71)
LOCATE 7, 58: COLOR CLOR(69), 0: PRINT SMFB$(69)
LOCATE 8, 58: COLOR CLOR(69), 0: PRINT SMFB$(69)
LOCATE 11, 58: COLOR CLOR(67), 0: PRINT SMFB$(67)
LOCATE 12, 58: COLOR CLOR(67), 0: PRINT SMFB$(67)
 COLOR 7, 0

FOR I = 1 TO 7
    IF TRACKSOUTH(I) = 1 THEN
     CLOR(I) = 2
     LOCATE I + 10, 1
     COLOR CLOR(I), 0
     PRINT "S Yard Track#"; : PRINT I
     CLOR(I) = 7
    END IF

    IF TRACKNORTH(I) = 1 THEN
     CLOR(I) = 2
     LOCATE I + 10, 1
     COLOR CLOR(I), 0
     PRINT "N Yard Track#"; : PRINT I
     CLOR(I) = 7
    END IF

NEXT I

FOR I = 0 TO 16
        IF PB(I) <> 0 THEN
         LOCATE 4, 65: PRINT "Push Button "; : PRINT I
          'BEEP
          GOTO 200
        ELSE
        END IF
NEXT I
200

COLOR 7, 0
Finish! = TIMER

GOTO LastReport

Latonia: REM ********************* LATONIA *************************

IF Report$ <> "Latonia" THEN CLS : CALL HEADER: Report$ = "Latonia"

LOCATE 5, 7: PRINT "Latonia"
FOR I = 18 TO 25
 IF BLK(I) = 1 THEN
  CLOR(I) = 4
 ELSE
  CLOR(I) = 7
 END IF
NEXT I
IF BLK(168) = 1 THEN CLOR(68) = 4 ELSE CLOR(68) = 7
IF BLK(169) = 1 THEN CLOR(69) = 4 ELSE CLOR(69) = 7
IF BLK(170) = 1 THEN CLOR(70) = 4 ELSE CLOR(70) = 7

LOCATE 7, 1: COLOR CLOR(19), 0: PRINT "Latonia Wye Main N  "
LOCATE 8, 1: COLOR CLOR(18), 0: PRINT "Latonia Wye Main S  "
LOCATE 9, 1: COLOR CLOR(70), 0: PRINT "SW #65 Drill I-lock  "
LOCATE 10, 1: COLOR CLOR(69), 0: PRINT "Latonia Main S     "
LOCATE 11, 1: COLOR CLOR(68), 0: PRINT "Latonia Main N     "
LOCATE 12, 1: COLOR CLOR(21), 0: PRINT "SW 59 X/O Main N   "
LOCATE 13, 1: COLOR CLOR(20), 0: PRINT "SW 59 X/O Main S   "
LOCATE 14, 1: COLOR CLOR(22), 0: PRINT "South Main         "
LOCATE 15, 1: COLOR CLOR(23), 0: PRINT "South Siding       "
LOCATE 16, 1: COLOR CLOR(24), 0: PRINT "SW #57 Interlock   "
LOCATE 17, 1: COLOR CLOR(25), 0: PRINT "SW #55 Interlock   "
LOCATE 18, 1: COLOR CLOR(26), 0: PRINT "South Main         "

FOR I = 55 TO 65 STEP 2
IF SMFBN(I) = 1 THEN
 SMFB$(I) = "N":
 CLOR(I) = 7
ELSE
 SMFB$(I) = "R":
 CLOR(I) = 4
END IF
NEXT I

LOCATE 9, 20: COLOR CLOR(65), O: PRINT SMFB$(65)
LOCATE 10, 20: COLOR CLOR(63), O: PRINT SMFB$(63)
LOCATE 11, 20: COLOR CLOR(61), O: PRINT SMFB$(61)
LOCATE 12, 20: COLOR CLOR(59), O: PRINT SMFB$(59)
LOCATE 16, 20: COLOR CLOR(57), O: PRINT SMFB$(57)
LOCATE 17, 20: COLOR CLOR(55), O: PRINT SMFB$(55)

FOR I = 22 TO 36
        IF PB(I) = 1 THEN
         LOCATE 7, 65: PRINT "Push Button "; : PRINT I
         'BEEP
          GOTO 250
        ELSE
        END IF
NEXT I
250

Finish! = TIMER
COLOR 7, 0

GOTO LastReport

Walton: REM ******************* WALTON ***************************
IF Report$ <> "Walton" THEN Report$ = "Walton"
LOCATE 5, 32: PRINT Report$
FOR I = 26 TO 34
 IF BLK(I) = 1 THEN
  CLOR(I) = 4
 ELSE
  CLOR(I) = 7
 END IF
NEXT I

LOCATE 7, 25: COLOR CLOR(27), O: PRINT "North Main          "
LOCATE 8, 25: COLOR CLOR(26), O: PRINT "SW #53 Interlock    "
LOCATE 9, 25: COLOR CLOR(29), O: PRINT "Main                "
LOCATE 10, 25: COLOR CLOR(30), O: PRINT "SW #51 Interlock    "
LOCATE 11, 25: COLOR CLOR(28), O: PRINT "Siding west         "
LOCATE 12, 25: COLOR CLOR(31), O: PRINT "Siding east         "
LOCATE 13, 25: COLOR CLOR(32), O: PRINT "SW #49 Interlock    "
LOCATE 14, 25: COLOR CLOR(33), O: PRINT "SW #47 Interlock    "
LOCATE 15, 25: COLOR CLOR(34), O: PRINT "South Main          "

FOR I = 47 TO 53 STEP 2
IF SMFBN(I) = 1 THEN
 SMFB$(I) = "N":  
 CLOR(I) = 7
ELSE
 SMFB$(I) = "R":
 CLOR(I) = 4
END IF
NEXT I

LOCATE 8, 45: COLOR CLOR(53), O: PRINT SMFB$(53)
LOCATE 10, 45: COLOR CLOR(51), O: PRINT SMFB$(51)
LOCATE 13, 45: COLOR CLOR(49), O: PRINT SMFB$(49)
LOCATE 14, 45: COLOR CLOR(47), O: PRINT SMFB$(47)

COLOR 7, 0
Finish! = TIMER

GOTO LastReport

Sparta: REM ******************* SPARTA ***************************
IF Report$ <> "Sparta" THEN Report$ = "Sparta"
LOCATE 5, 57: PRINT Report$
FOR I = 34 TO 45
 IF BLK(I) = 1 THEN
  CLOR(I) = 4
 ELSE
  CLOR(I) = 7
 END IF
NEXT I

LOCATE 7, 50: COLOR CLOR(34), O: PRINT "North Main          "
LOCATE 8, 50: COLOR CLOR(37), 0: PRINT "SW #45 Interlock    "
LOCATE 9, 50: COLOR CLOR(38), 0: PRINT "SW #43 Interlock    "
LOCATE 10, 50: COLOR CLOR(39), 0: PRINT "Main                "
LOCATE 11, 50: COLOR CLOR(40), 0: PRINT "Siding west         "
LOCATE 12, 50: COLOR CLOR(41), 0: PRINT "Siding east         "
LOCATE 13, 50: COLOR CLOR(42), 0: PRINT "SW #41 Interlock    "
LOCATE 14, 50: COLOR CLOR(43), 0: PRINT "Mid Main            "
LOCATE 15, 50: COLOR CLOR(44), 0: PRINT "SW #39 Interlock    "
LOCATE 16, 50: COLOR CLOR(45), 0: PRINT "South Main          "

FOR I = 39 TO 45 STEP 2
  IF SMFBN(I) = 1 THEN
   SMFB$(I) = "N"
   CLOR(I) = 7
  ELSE
   SMFB$(I) = "R"
   CLOR(I) = 4
  END IF
NEXT I

LOCATE 8, 70:  COLOR CLOR(45), 0: PRINT SMFB$(45)
LOCATE 9, 70:  COLOR CLOR(43), 0: PRINT SMFB$(43)
LOCATE 13, 70: COLOR CLOR(41), 0: PRINT SMFB$(41)
LOCATE 15, 70: COLOR CLOR(39), 0: PRINT SMFB$(39)

COLOR 7, 0
Finish! = TIMER

GOTO LastReport


Worthville: REM ******************* WORTHVILLE ***************************
IF Report$ <> "Worthville" THEN CLS : CALL HEADER: Report$ = "Worthville"
LOCATE 5, 10: PRINT Report$
FOR I = 45 TO 73
 IF BLK(I) = 1 THEN
  CLOR(I) = 4
 ELSE
  CLOR(I) = 7
 END IF
NEXT I

LOCATE 7, 1:  COLOR CLOR(45), O: PRINT "North Main          "
LOCATE 8, 1:  COLOR CLOR(49), O: PRINT "SW #37 Interlock    "
LOCATE 9, 1:  COLOR CLOR(50), O: PRINT "Main; Blk(50)       "
LOCATE 10, 1: COLOR CLOR(51), O: PRINT "W Siding; BLK(51)   "
LOCATE 11, 1: COLOR CLOR(52), O: PRINT "SW #35 Interlock    "
LOCATE 12, 1: COLOR CLOR(56), O: PRINT "Interchange Siding  "
LOCATE 13, 1: COLOR CLOR(53), O: PRINT "SW #33 X/O east     "
LOCATE 14, 1: COLOR CLOR(58), O: PRINT "SW #33 X/O west     "
LOCATE 15, 1: COLOR CLOR(55), O: PRINT "Mid Main  BLK(55)   "
LOCATE 16, 1: COLOR CLOR(54), O: PRINT "East Siding         "
LOCATE 17, 1: COLOR CLOR(59), O: PRINT "SW #31 X/O main     "
LOCATE 18, 1: COLOR CLOR(60), O: PRINT "SW #31 X/O siding   "
LOCATE 19, 1: COLOR CLOR(62), O: PRINT "SW #29 Interlock    "
LOCATE 20, 1: COLOR CLOR(73), O: PRINT "South Main          "
LOCATE 21, 1: COLOR CLOR(69), 0: PRINT "Carrolton RR        "

FOR I = 29 TO 37 STEP 2
IF SMFBN(I) = 1 THEN
 SMFB$(I) = "N":
 CLOR(I) = 7
ELSE
 SMFB$(I) = "R":
 CLOR(I) = 4
END IF
NEXT I

LOCATE 8, 20: COLOR CLOR(37), 0: PRINT SMFB$(37)
LOCATE 11, 20: COLOR CLOR(35), 0: PRINT SMFB$(35)
LOCATE 13, 20: COLOR CLOR(33), 0: PRINT SMFB$(33)
LOCATE 14, 20: COLOR CLOR(33), 0: PRINT SMFB$(33)
LOCATE 17, 20: COLOR CLOR(31), 0: PRINT SMFB$(31)
LOCATE 18, 20: COLOR CLOR(31), 0: PRINT SMFB$(31)
LOCATE 19, 20: COLOR CLOR(29), 0: PRINT SMFB$(29)

COLOR 7, 0
Finish! = TIMER

GOTO LastReport

Campbellsburg: REM ******************* CAMPBELLSBURG ***************************
IF Report$ <> "Campbellsburg" THEN Report$ = "Campbellsburg"
LOCATE 5, 39: PRINT Report$

FOR I = 73 TO 84
 IF BLK(I) = 1 THEN
  CLOR(I) = 4
 ELSE
  CLOR(I) = 7
 END IF
NEXT I

LOCATE 7, 30:  COLOR CLOR(73), O: PRINT "North Main          "
LOCATE 8, 30: COLOR CLOR(74), 0: PRINT "SW #27 Interlock    "
LOCATE 9, 30: COLOR CLOR(75), 0: PRINT "Main N              "
LOCATE 10, 30: COLOR CLOR(76), 0: PRINT "W Siding            "
LOCATE 11, 30: COLOR CLOR(77), 0: PRINT "SW #25 Interlock    "
LOCATE 12, 30: COLOR CLOR(78), 0: PRINT "SW #23 Interlock    "
LOCATE 13, 30: COLOR CLOR(80), 0: PRINT "SW #21 Interlock    "
LOCATE 14, 30: COLOR CLOR(81), 0: PRINT "E Siding            "
LOCATE 15, 30: COLOR CLOR(79), 0: PRINT "SW #19 Interlock    "
LOCATE 16, 30: COLOR CLOR(82), 0: PRINT "Main S              "
LOCATE 17, 30: COLOR CLOR(83), 0: PRINT "SW #17 Interlock    "
LOCATE 18, 30: COLOR CLOR(84), 0: PRINT "South Main          "

FOR I = 17 TO 27 STEP 2
 IF SMFBN(I) = 1 THEN
  SMFB$(I) = "N"
  CLOR(I) = 7
 ELSE
  SMFB$(I) = "R"
  CLOR(I) = 4
 END IF
NEXT I
LOCATE 8, 52: COLOR CLOR(27), 0: PRINT SMFB$(27)
LOCATE 11, 52: COLOR CLOR(25), 0: PRINT SMFB$(25)
LOCATE 12, 52: COLOR CLOR(23), 0: PRINT SMFB$(23)
LOCATE 13, 52: COLOR CLOR(21), 0: PRINT SMFB$(21)
LOCATE 15, 52: COLOR CLOR(19), 0: PRINT SMFB$(19)
LOCATE 17, 52: COLOR CLOR(17), 0: PRINT SMFB$(17)

COLOR 7, 0
Finish! = TIMER

GOTO LastReport


CTCmach:
IF Report$ <> "CTC Machine" THEN CLS : CALL HEADER: Report$ = "CTC Machine"
LOCATE 5, 10: PRINT Report$
LOCATE 6, 10: PRINT "status"; : PRINT ""

Finish! = TIMER
COLOR 7, 0
GOTO LastReport

LastReport:

END SUB

SUB CTCBOARD
CALL HEADER

REM **** Variables for Flashing RED, Green & Yellow for signals and control panels
FRED = RED: FRED1 = DRK: FRED2 = DRK
FGRN = GRN: FGRN1 = DRK: FGRN2 = DRK
FYEL = YEL: FYEL1 = DRK: FYEL2 = DRK
FREDB = REDB: FREDB1 = DRK: FREDB2 = DRK
FREDGRN = RED: FREDGRN1 = GRN: FREDGRN2 = GRN
REDFRED = 32: REDFRED1 = 36: REDFRED2 = 36
REDREDFYELB = REDREDYELB: REDREDFYELB1 = 36: REDREDFYELB2 = 36


REM ********* Warning if switch motors are REV on startup *******************
CALL READRR
FOR I = 17 TO 67 STEP 2
   IF SWITCHREV(I) = 1 THEN
    LED(I) = 1: UL(I) = 1
    SM(I) = TUR
   ELSE
    LED(I) = 0: UL(I) = 0
    SM(I) = TUN
   END IF
NEXT I

CALL WRITERR

REM ************* GET TIME FOR FAST CLOCK ***************************
T$ = TIME$: ' real time
StartFC! = TIMER: ' base start point of the computer clock
                        'in sceonds this day real time
BRTL:
'****************** FAST CLOCK CALCULATIONS *************************

FinishFC! = TIMER
LapsTime! = FinishFC! - StartFC!: ' time lapst from start
FastClock! = LapsTime! * Ratio: ' real time in seconds pasted x fast clock ratio
Seconds! = INT(FastClock!)
'Mins = INT(FastClock! / 60)
IF Seconds! > 59 THEN Seconds! = 0: Mins = Mins + 1: StartFC! = TIMER
IF Mins > 59 THEN Mins = 0: Hours = Hours + 1
IF Hours > 23 THEN Hours = 0
Sec$ = LTRIM$(STR$(Seconds!)): IF Seconds! < 10 THEN Sec$ = "0" + Sec$
Min$ = LTRIM$(STR$(Mins)): IF Mins < 10 THEN Min$ = "0" + Min$
Hour$ = LTRIM$(STR$(Hours)): IF Hours < 10 THEN Hour$ = "0" + Hour$
TimeOfDay = 60 * Hours + Mins

' Flashing LED Software
CheckTime1! = TIMER
IF CheckTime1! > CheckTime2! + 1 THEN
  CheckTime2! = TIMER
  FRED1 = FRED: FRED = FRED2: FRED2 = FRED1
  FGRN1 = FGRN: FGRN = FGRN2: FGRN2 = FGRN1
  FYEL1 = FYEL: FYEL = FYEL2: FYLE2 = FYEL1
  FREDB1 = FREDB: FREDB = FREDB2: FREDB2 = FREDB1
  FREDGRN1 = FREDGRN: FREDGRN = FREDGRN2: FREDGRN2 = FREDGRN1
  REDFRED1 = REDFRED: REDFRED = REDFERD2: REDFRED2 = REDFRED1
  REDREDFYELB1 = REDREDFYELB: REDREDFYELB = REDREDFYELB2: REDREDFYELB2 = REDREDFYELB1
END IF

CALL READRR

REM **************** DeCoursey Yard **********************
' Check control panel for press of pushbutton, then align switches
FOR I = 0 TO 16
 IF PB(I) <> 0 THEN
   PB = I
   LOCATE 5, 65: PRINT "PUSH BUTTON "; : PRINT I
   GOTO AlignSwitchDeC
 END IF
NEXT I
' Aligns switches acording to pushbuttons pressed as read above
AlignSwitchDeC:
SELECT CASE PB
       CASE 0: 'South Main to Carrolton RR
       IF BLK(2) <> OCC THEN
        IF BLK(171) <> OCC THEN
         SM(108) = TUN
         SM(111) = TUN
         SM(71) = TUR
        END IF
       END IF
       CASE 1: ' Main South RH to Latonia
        IF BLK(15) + BLK(173) < OCC THEN
         SM(101) = TUN
         SM(105) = TUN
         SM(69) = TUN
        END IF
       CASE 2: ' Main North LH around Latonia
        IF BLK(15) + BLK(173) < OCC THEN
         SM(101) = TUN
         SM(105) = TUN
         SM(69) = TUR
        END IF
       CASE 3: ' DeCoursey North #7
        IF BLK(11) <> OCC THEN
         SM(101) = TUN
         SM(105) = TUR
         SM(106) = TUN
         SM(111) = TUN
        END IF
       CASE 4: ' DeCoursey North #6
        IF BLK(11) <> OCC THEN
         SM(101) = TUN
         SM(105) = TUR
         SM(106) = TUR
         SM(107) = TUN
         END IF
       CASE 5: ' DeCoursey North #5
        IF BLK(11) <> OCC THEN
         SM(101) = TUN
         SM(105) = TUR
         SM(106) = TUR
         SM(107) = TUR
         END IF
       CASE 6: ' DeCoursey North #4
        IF BLK(11) <> OCC THEN
         SM(101) = TUR
         SM(102) = TUN
         SM(104) = TUN
         END IF
       CASE 7: ' DeCoursey North #3
        IF BLK(11) <> OCC THEN
         SM(101) = TUR
         SM(102) = TUN
         SM(104) = TUR
        END IF
       CASE 8: ' DeCoursey North #2
        IF BLK(11) <> OCC THEN
         SM(101) = TUR
         SM(102) = TUR
         SM(103) = TUN
        END IF
       CASE 9: ' DeCoursey North #1
        IF BLK(11) <> OCC THEN
         SM(101) = TUR
         SM(102) = TUR
         SM(103) = TUR
        END IF
       CASE 10: ' DeCoursey South #1
        IF BLK(2) <> OCC THEN
         SM(108) = TUR
         SM(109) = TUR
         SM(110) = TUR
        END IF
       CASE 11: ' DeCoursey South #2
        IF BLK(2) <> OCC THEN
         SM(108) = TUR
         SM(109) = TUR
         SM(110) = TUN
        END IF
       CASE 12: ' DeCoursey South #3
        IF BLK(2) <> OCC THEN
         SM(108) = TUR
         SM(109) = TUN
        END IF
       CASE 13: ' DeCoursey South #4
        IF BLK(2) <> OCC THEN
         SM(108) = TUN
         SM(111) = TUR
         SM(112) = TUR
        END IF
       CASE 14: ' DeCoursey South #5
        IF BLK(2) <> OCC THEN
         SM(108) = TUN
         SM(111) = TUR
         SM(112) = TUN
         SM(113) = TUR
        END IF
       CASE 15: ' DeCoursey South #6
        IF BLK(2) <> OCC THEN
         SM(108) = TUN
         SM(111) = TUR
         SM(112) = TUN
         SM(113) = TUN
         SM(114) = TUR
        END IF
       CASE 16: ' DeCoursey South #7
        IF BLK(2) <> OCC THEN
         SM(108) = TUN
         SM(111) = TUR
         SM(112) = TUN
         SM(113) = TUN
         SM(114) = TUN
        END IF
       CASE ELSE
        'PRINT "ERROR OUT OF RANGE, DeCoursey YARD LADDER SELECTION!": BEEP
       END SELECT

      
REM **** Logic statements for DeCoursey Yard Control Panel LEDS

        IF BLK(1) + BLK(65) + BLK(68) >= OCC THEN LED(121) = 1 ELSE LED(121) = 0
        IF BLK(2) = OCC THEN LED(120) = 1 ELSE LED(120) = 0

        IF BLK(11) = OCC THEN LED(119) = 1 ELSE LED(119) = 0
        ' BLK(12) is approach to crossing. This energizes a relay as appropriate to change polarity of crossing.

        ' Switch 69
        LED(117) = 0: LED(118) = 0
        IF SMFBN(69) = 1 THEN LED(117) = FGRN ELSE LED(118) = FGRN
        IF BLK(13) = OCC THEN LED(118) = 1
        IF BLK(14) = OCC THEN LED(117) = 1
        IF BLK(15) = OCC THEN LED(117) = 1
        IF BLK(173) = OCC THEN LED(118) = 1
        
' Auto Correct logic to be removed once DS has control of this section of track
'        IF BLK(13) = OCC THEN
'          SM(69) = TUN
'          SM(101) = TUN
'          SM(105) = TUN
'         ELSE
'          IF BLK(14) = OCC THEN
'          SM(69) = TUR
'          SM(101) = TUN
'          SM(105) = TUN
'         END IF
'        END IF

' Reset all Relays to off
   FOR J = 1 TO 7
    Relay(J) = 0
   NEXT J

' Track #1 N
       
        IF TRACKNORTH(1) = 1 THEN
          Relay(1) = 1
          IF BLK(4) = 0 THEN LED(107) = GRN ELSE LED(107) = FRED
         ELSE
          IF BLK(4) = OCC THEN LED(107) = RED ELSE LED(107) = DRK
        END IF

' Track #2 N
        IF TRACKNORTH(2) = 1 THEN
        Relay(2) = 1
          IF BLK(5) = 0 THEN LED(106) = GRN ELSE LED(106) = FRED
         ELSE
          IF BLK(5) = OCC THEN LED(106) = RED ELSE LED(106) = DRK
        END IF

' Track #3 N
        IF TRACKNORTH(3) = 1 THEN
        Relay(3) = 1
          IF BLK(6) = 0 THEN LED(105) = GRN ELSE LED(105) = FRED
         ELSE
          IF BLK(6) = OCC THEN LED(105) = RED ELSE LED(105) = DRK
        END IF

' Track #4 N
        IF TRACKNORTH(4) = 1 THEN
          Relay(4) = 1
          IF BLK(7) = 0 THEN LED(104) = GRN ELSE LED(104) = FRED
         ELSE
          IF BLK(7) = OCC THEN LED(104) = RED ELSE LED(104) = DRK
        END IF

' Track #5 N
        IF TRACKNORTH(5) = 1 THEN
          Relay(5) = 1
          IF BLK(8) = 0 THEN LED(103) = GRN ELSE LED(103) = FRED
         ELSE
          IF BLK(8) = OCC THEN LED(103) = RED ELSE LED(103) = DRK
        END IF

' Track #6 N
        IF TRACKNORTH(6) = 1 THEN
          Relay(6) = 1
          IF BLK(9) = 0 THEN LED(102) = GRN ELSE LED(102) = FRED
         ELSE
          IF BLK(9) = OCC THEN LED(102) = RED ELSE LED(102) = DRK
        END IF

' Track #7 N
        IF TRACKNORTH(7) = 1 THEN
          Relay(7) = 1
          IF BLK(10) = 0 THEN LED(101) = GRN ELSE LED(101) = FRED
          IF SMFBN(117) <> TUN THEN LED(101) = RED
         ELSE
          IF BLK(10) = OCC THEN LED(101) = RED ELSE LED(101) = DRK
        END IF
        LED(101) = GRN
' Track #1 S
        IF TRACKSOUTH(1) = 1 THEN
          Relay(1) = 1
          IF BLK(4) = 0 THEN LED(115) = GRN ELSE LED(115) = FRED
         ELSE
          IF BLK(4) = OCC THEN LED(115) = RED ELSE LED(115) = DRK
        END IF

' Track #2 S
        IF TRACKSOUTH(2) = 1 THEN
          Relay(2) = 1
          IF BLK(5) = 0 THEN LED(114) = GRN ELSE LED(114) = FRED
         ELSE
          IF BLK(5) = OCC THEN LED(114) = RED ELSE LED(114) = DRK
        END IF

' Track #3 S
        IF TRACKSOUTH(3) = 1 THEN
          Relay(3) = 1
          IF BLK(6) = 0 THEN LED(113) = GRN ELSE LED(113) = FRED
         ELSE
          IF BLK(6) = OCC THEN LED(113) = RED ELSE LED(113) = DRK
        END IF

' Track #4 S
        IF TRACKSOUTH(4) = 1 THEN
          Relay(4) = 1
          IF BLK(7) = 0 THEN LED(112) = GRN ELSE LED(112) = FRED
         ELSE
          IF BLK(7) = OCC THEN LED(112) = RED ELSE LED(112) = DRK
        END IF

' Track #5 S
        IF TRACKSOUTH(5) = 1 THEN
          Relay(5) = 1
          IF BLK(8) = 0 THEN LED(111) = GRN ELSE LED(111) = FRED
         ELSE
          IF BLK(8) = OCC THEN LED(111) = RED ELSE LED(111) = DRK
        END IF

' Track #6 S
        IF TRACKSOUTH(6) = 1 THEN
          Relay(6) = 1
          IF BLK(9) = 0 THEN LED(110) = GRN ELSE LED(110) = FRED
          IF SMFBN(115) <> TUN THEN LED(110) = RED
         ELSE
          IF BLK(9) = OCC THEN LED(110) = RED ELSE LED(110) = DRK
        END IF

' Track #7 S
        IF TRACKSOUTH(7) = 1 THEN
          Relay(7) = 1
          IF BLK(10) = 0 THEN LED(109) = GRN ELSE LED(109) = FRED
          IF SMFBN(116) <> TUN THEN LED(109) = RED
          IF SMFBN(118) <> TUN THEN LED(109) = RED
         ELSE
          IF BLK(10) = OCC THEN LED(109) = RED ELSE LED(109) = DRK
        END IF


DST:
' Diesel Service Track #1
          LED(108) = DRK
          IF SWITCHN(3) = 1 THEN LED(108) = FREDGRN: 'program mode
          IF SWITCHREV(3) = 1 THEN LED(108) = GRN
' Diesel Service Track #2
          LED(116) = DRK
          IF SWITCHN(2) = 1 THEN LED(116) = FREDGRN: 'program mode
          IF SWITCHREV(2) = 1 THEN LED(116) = GRN
' Test Service Track #1
          'SWITCHN(1) AND SWITCHREV(1) read but nothing dispalyed for the removable test track.


REM ************ Latonia Yard *********************

FOR I = 22 TO 36
 IF PB(I) <> 0 THEN
   PB = I
   GOTO AlignSwitchLat
 END IF
NEXT I

AlignSwitchLat:
SELECT CASE PB
       CASE 0: 'No Selection Made this time
       CASE 22: 'Drill
        IF BLK(170) = 0 THEN SM(65) = TUR
       CASE 23: ' North Siding
        IF BLK(170) = 0 THEN SM(65) = TUN
       CASE 24: ' A/D shortcut
        SM(63) = TUR
        SM(131) = TUR
       CASE 25: ' Siding
        SM(63) = TUN
        SM(131) = TUN
       CASE 26: ' A/D from drill
        SM(127) = TUN
        SM(128) = TUN
        SM(129) = TUN
        SM(130) = TUN
        SM(131) = TUN
        SM(63) = TUN
       CASE 27: ' Track #1 North
        SM(127) = TUN
        SM(128) = TUN
        SM(129) = TUN
        SM(130) = TUR
       CASE 28: ' Track #2 North
        SM(127) = TUN
        SM(128) = TUN
        SM(129) = TUR
       CASE 29:  ' Track #3 North
        SM(127) = TUN
        SM(128) = TUR
       CASE 30: ' Track #4 North
        SM(127) = TUR
       CASE 31: ' Track #4 South
         SM(139) = TUN
         SM(140) = TUN
         SM(141) = TUN
         SM(142) = TUN
        IF BLK(24) = 0 THEN
         SM(57) = TUR
        END IF
       CASE 32: ' Track #3 South
         SM(139) = TUR
         SM(140) = TUN
         SM(141) = TUN
         SM(142) = TUN
        IF BLK(24) = 0 THEN
         SM(57) = TUR
        END IF
       CASE 33:  ' Track #2 South
         SM(140) = TUR
         SM(141) = TUN
         SM(142) = TUN
        IF BLK(24) = 0 THEN
         SM(57) = TUR
        END IF
       CASE 34: ' Track #1 South
         SM(141) = TUR
         SM(142) = TUN
        IF BLK(24) = 0 THEN
         SM(57) = TUR
        END IF
       CASE 35:  ' A/D Track South
         SM(142) = TUR
        IF BLK(24) = 0 THEN
         SM(57) = TUR
        END IF
       CASE 36:  ' Siding SOUTH
        IF BLK(24) = 0 THEN SM(57) = TUN
       CASE ELSE
        'PRINT "ERROR OUT OF RANGE, Latonia YARD LADDER SELECTION! ";
       END SELECT

      PB = -1 'Reset push button inputs to = -1 No push button pressed
        
      Light(1) = 0
      IF BLK(18) = OCC THEN Light(1) = 1: 'Approaching train from Latonia N Mail turns on light in Tower DeCoursey
      IF BLK(19) = OCC THEN Light(1) = 1
      IF BLK(169) = OCC THEN Light(1) = 1
      IF BLK(170) = OCC THEN Light(1) = 1



CALL SWLOCKS

'  LOCATE 9, 70: PRINT TIMER;



800


CALL TIMERCNT
CALL ABSIGNALS
' Timer and indicator to trace real time loop. LED(108) on DeCoursey panel D/S#1
LoopCount = LoopCount + 1
 IF LoopCount = 10 THEN LED(108) = RED: LoopCount = 0: ' at 10th loop turn on LED(108) and reset count

CALL WRITERR
LED(108) = 0: 'Turn indicator off

IF Diagnose$ = "Y" THEN CALL CRTDISPLAY
LOCATE 23, 27: PRINT "Press [ESC] to stop program"
IF INKEY$ = CHR$(27) THEN END

GOTO BRTL


END SUB

SUB FastClk

CLS


LOCATE 2, 25: PRINT "Set Fast Clock"

GetRatio:
LOCATE 4, 25: PRINT "FAST CLOCK RATIO   "; : PRINT Ratio;
LOCATE 4, 45: INPUT "", Ratio1
 IF Ratio1 > 24 OR Ratio1 < 0 THEN
  LOCATE 4, 50: BEEP: PRINT "OUT OF RANGE"
  GOTO GetRatio
 END IF
 IF Ratio1 <> 0 THEN Ratio = Ratio1

GetHour:
LOCATE 6, 25: PRINT "STARTING HOUR      "; : PRINT USING "##"; Hours; : PRINT ":"; : PRINT USING "##"; Mins;
LOCATE 6, 45: INPUT "", Hours1
 IF Hours1 > 24 OR Hours1 < 0 THEN
  LOCATE 6, 50: BEEP: PRINT "OUT OF RANGE"
  GOTO GetHour
 END IF
 IF Hours1 <> 0 THEN Hours = Hours1

GetMin:
LOCATE 6, 47: INPUT "", Mins1
 IF Mins1 > 60 OR Mins1 < 0 THEN
  LOCATE 6, 50: BEEP: PRINT "OUT OF RANGE"
  GOTO GetMin
 END IF
 IF Mins1 <> 0 THEN Mins = Mins1

Filenum% = FREEFILE
File$ = "FASTCLK.DAT"
OPEN File$ FOR OUTPUT AS Filenum%
WRITE #Filenum%, Ratio, Hours, Mins
CLOSE #Filenum%

END SUB

SUB HEADER
REM**PRINTOUT TITLE
       CLS
       LOCATE 2, 25: PRINT "Louisville & Nashville Railroad"
       LOCATE 3, 32: PRINT "LC&L Subdivision"
       LOCATE 3, 66: PRINT VERSION$
END SUB

SUB INIT
  REM***************************************************
  REM********SERIAL PROTOCOL SUBROUTINES****************
  REM*************QB4.5 CALL VERSION********************
  REM     SPSQBC01.BAS    DATED: JUNE 30, 2003         **
  REM (Enhanced version for use with QuickBASIC V4.5) **
  REM    FOR USIC, SUSIC AND SMINI APPLICATIONS       **
  REM***************************************************
  REM**EACH SPS PACKAGE CONTAINS 5 SEPARATE SUBROUTINES DEFINED AS:
     '1) INIT    -- Invoked by application program to initialize node
     '2) INPUTS  -- Invoked by application program to read input bytes...
                     '...IB(1) up through IB(NI) from the interface hardware
                     'where NI = number of input ports contaned within node
     '3) OUTPUTS -- Invoked by application program to write output bytes...
                     '...OB(1) up through OB(NO) to the interface hardware
                     'where NO = number of output ports contained within node
     '4) RXBYTE  -- Used by INPUTS to read an input byte (INBYTE) into...
                     '...the PC receive buffer from the interface hardware
     '5) TXPACK  -- Used by INIT, INPUTS and OUTPUTS to formulate and...
                     '...transmit data packet from PC to interface hardware

  REM**********************************************
  REM**                ***INIT***                **
  REM**************QB4.5 CALL VERSION**************
  REM**     SUBROUTINE TO INITIALIZE NODE        **
  REM** for use with USIC, SUSIC and SMINI nodes **
  REM**********************************************

    '**NOTE: This subroutine must be executed correctly prior to...
    '        ...invoking INPUTS and OUTPUTS subroutines
    ' Following parameters must be defined in the application...
    '           ...program prior to invoking INIT:
    '       UA       = USIC address (range 0 to 127) unless using...
    '                ... Classic USIC with 68701 then range is 0 to 15
    '       COMPORT  = PC COM port = 1, 2, 3 or 4
    '       BAUD100  = PC baud rate divided by 100
    '       DL       = USIC transmission delay
    '       NDP$     = Node definition parameter = "M", "N" or "X"
    '       NI       = Number of input ports contained within node
    '       NO       = Number of output ports contained within node
    '       MAXTRIES = Maximum number of PC tries to read input...
    '                  ...bytes prior to PC aborting inputs
    'For SMINI applications:
    '       NS       = Number of 2-lead searchlight signals...
    '                  ...requiring yellow oscillation feature
    'Only for SMINI case when NS > 0 i.e. signals are present
    '       CT(1) through CT(6) = Card type definition elements...
    '             ...defining signal bit locations within each...
    '             ...of the SMINI's 6 output ports
    'For SUSIC and USIC applications:
    '       NS       = Number of I/O card sets of 4
    '       CT(1) through CT(NS) = Card type definition elements...
    '             ...defining the card type arrangement within...
    '             ...each set of 4 cards

   REM**BEGIN INITIALIZATION OF USIC, SUSIC OR SMINI
   REM**Initialize intries counter and initialization error flag
      INTRIES = 0     'Initialize INTRIES counter to zero
      INITERR = 0     'Initialize error flag to zero

   REM**CHECK FOR VALID RANGE OF USIC ADDRESS
        'NOTE: Range 0 - 15 is not checked for Classic USIC with 68701
      IF UA > 127 THEN
         PRINT "**ERROR** UA = "; UA; " Out of range 0 to 127"
         INITERR = 1
      END IF

   REM**CHECK FOR VALID NUMBER FOR PC COM PORT (COM1 THRU COM4)...
        '...and if valid number, assign Port Address
      IF COMPORT = 1 THEN PA = 1016: GOTO COMOK
      IF COMPORT = 2 THEN PA = 760: GOTO COMOK
      IF COMPORT = 3 THEN PA = 1000: GOTO COMOK
      IF COMPORT = 4 THEN PA = 744: GOTO COMOK
      PRINT "**ERROR** COMPORT = "; COMPORT; " MUST = 1, 2, 3 OR 4"
      INITERR = 1
COMOK:
                                       
   REM**CHECK FOR VALID BAUD RATE AND IF VALID SET LOWER ORDER BAUD LATCH
      IF BAUD100 = 96 THEN BAUDLS = 12: GOTO BAUDOK
      IF BAUD100 = 192 THEN BAUDLS = 6: GOTO BAUDOK
      IF BAUD100 = 288 THEN BAUDLS = 4: GOTO BAUDOK
      IF BAUD100 = 576 THEN BAUDLS = 2: GOTO BAUDOK
      IF BAUD100 = 1152 THEN BAUDLS = 1: GOTO BAUDOK
      PRINT "**ERROR** BAUD100 = "; BAUD100
      PRINT "Valid BAUD100 values are 96, 192, 228, 576 and 1152"
      INITERR = 1
BAUDOK:

   REM**CHECK FOR VALID NODE DEFINITION PARAMETER AND BRANCH ACCORDINGLY
      IF NDP$ = "M" THEN GOTO CHKMINI
      IF NDP$ = "N" THEN GOTO CHKMAXI
      IF NDP$ = "X" THEN GOTO CHKMAXI
      PRINT "***ERROR*** NDP$ = "; NDP$; " must be set to M, N, OR X "
      PRINT "****INITIALIZATION TERMINATED DUE TO INVALID NDP$****"
      INITERR = 1
      GOTO INITRET

CHKMINI:
   REM*************BEGIN SMINI SPECIFIC PARAMETER CHECKING************
   REM**CHECK FOR VALID NI, NO AND NS USING SMINI
      IF NI <> 3 THEN
        PRINT "INVALID NI = "; NI; "MUST BE NI = 3 FOR SMINI"
        INITERR = 1
      END IF

      IF NO <> 6 THEN
        PRINT "INVALID NO = "; NO; "MUST BE NO = 6 FOR SMINI"
        INITERR = 1
      END IF
      
      IF NS = 0 THEN GOTO INCHKCMP   'No signals so branch to initialization...
                                     '...checking complete

   REM**SMINI HAS 2-LEAD OSCILLATING SIGNAL SO CHECK IF NS IN RANGE
      IF NS > 24 THEN
        PRINT "**ERROR** NS = "; NS; " OUT OF RANGE 0 TO 24 FOR SMINI"
        INITERR = 1
      END IF

   REM**CHECK FOR VALID CT ARRAY ELEMENTS WHILE COUNTING SIGNALS TO EQUAL NS
      NSCNT = 0        'Initialize signal count to zero
      FOR I = 1 TO 6   'Loop through 6 SMINI CT elements
         IF CT(I) = 0 THEN GOTO NEXTCT
         IF CT(I) = 3 THEN NSCNT = NSCNT + 1: GOTO NEXTCT
         IF CT(I) = 6 THEN NSCNT = NSCNT + 1: GOTO NEXTCT
         IF CT(I) = 12 THEN NSCNT = NSCNT + 1: GOTO NEXTCT
         IF CT(I) = 24 THEN NSCNT = NSCNT + 1: GOTO NEXTCT
         IF CT(I) = 48 THEN NSCNT = NSCNT + 1: GOTO NEXTCT
         IF CT(I) = 96 THEN NSCNT = NSCNT + 1: GOTO NEXTCT
         IF CT(I) = 192 THEN NSCNT = NSCNT + 1: GOTO NEXTCT
         IF CT(I) = 15 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 27 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 51 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 99 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 195 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 30 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 54 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 102 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 198 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 60 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 108 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 204 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 120 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 216 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 240 THEN NSCNT = NSCNT + 2: GOTO NEXTCT
         IF CT(I) = 63 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 123 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 243 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 111 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 207 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 219 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 126 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 222 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 246 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 252 THEN NSCNT = NSCNT + 3: GOTO NEXTCT
         IF CT(I) = 255 THEN NSCNT = NSCNT + 4: GOTO NEXTCT
         PRINT "**ERROR** INVALID CT("; I; ") = "; CT(I); " FOR SMINI"
         INITERR = 1
NEXTCT:
       NEXT I

       IF NSCNT <> NS THEN
          PRINT "**ERROR** SIGNAL COUNT FROM CTs <> NS FOR SMINI"
          INITERR = 1
    END IF
    GOTO INCHKCMP   'Proceed to initialization checking

   REM*************BEGIN SUSIC SPECIFIC PARAMETER CHECKING************
   REM**CHECK FOR VALID NS AND CTs USING USIC AND SUSIC
CHKMAXI:
      IF NS = 0 OR NS > 16 THEN
         PRINT "**ERROR** NS ="; NS; " OUT OF RANGE 1 TO 16 FOR SUSIC NODE"
         INITERR = 1
      END IF

     NICT = 0: NOCT = 0    'Initialize I/O type card counters to zero
  
 REM**GO THROUGH CT ELEMENT TO CHECK IF VALID AND COUNT I/O CARDS
      FOR I = 1 TO NS
         IF I = NS THEN  'Note: These CT( ) elements valid only for last card set
           IF CT(I) = 2 THEN NOCT = NOCT + 1: GOTO NEXTCTU
           IF CT(I) = 1 THEN NICT = NICT + 1: GOTO NEXTCTU
           IF CT(I) = 10 THEN NOCT = NOCT + 2: GOTO NEXTCTU
           IF CT(I) = 6 THEN NOCT = NOCT + 1: NICT = NICT + 1: GOTO NEXTCTU
           IF CT(I) = 9 THEN NOCT = NOCT + 1: NICT = NICT + 1: GOTO NEXTCTU
           IF CT(I) = 5 THEN NICT = NICT + 2: GOTO NEXTCTU
           IF CT(I) = 42 THEN NOCT = NOCT + 3: GOTO NEXTCTU
           IF CT(I) = 26 THEN NOCT = NOCT + 2: NICT = NICT + 1: GOTO NEXTCTU
           IF CT(I) = 38 THEN NOCT = NOCT + 2: NICT = NICT + 1: GOTO NEXTCTU
           IF CT(I) = 22 THEN NOCT = NOCT + 1: NICT = NICT + 2: GOTO NEXTCTU
           IF CT(I) = 41 THEN NOCT = NOCT + 2: NICT = NICT + 1: GOTO NEXTCTU
           IF CT(I) = 25 THEN NOCT = NOCT + 1: NICT = NICT + 2: GOTO NEXTCTU
           IF CT(I) = 37 THEN NOCT = NOCT + 1: NICT = NICT + 2: GOTO NEXTCTU
           IF CT(I) = 21 THEN NICT = NICT + 3: GOTO NEXTCTU
         END IF
         IF CT(I) = 170 THEN NOCT = NOCT + 4: GOTO NEXTCTU
         IF CT(I) = 106 THEN NOCT = NOCT + 3: NICT = NICT + 1: GOTO NEXTCTU
         IF CT(I) = 154 THEN NOCT = NOCT + 3: NICT = NICT + 1: GOTO NEXTCTU
         IF CT(I) = 90 THEN NOCT = NOCT + 2: NICT = NICT + 2: GOTO NEXTCTU
         IF CT(I) = 166 THEN NOCT = NOCT + 3: NICT = NICT + 1: GOTO NEXTCTU
         IF CT(I) = 102 THEN NOCT = NOCT + 2: NICT = NICT + 2: GOTO NEXTCTU
         IF CT(I) = 150 THEN NOCT = NOCT + 2: NICT = NICT + 2: GOTO NEXTCTU
         IF CT(I) = 86 THEN NOCT = NOCT + 1: NICT = NICT + 3: GOTO NEXTCTU
         IF CT(I) = 169 THEN NOCT = NOCT + 3: NICT = NICT + 1: GOTO NEXTCTU
         IF CT(I) = 105 THEN NOCT = NOCT + 2: NICT = NICT + 2: GOTO NEXTCTU
         IF CT(I) = 153 THEN NOCT = NOCT + 2: NICT = NICT + 2: GOTO NEXTCTU
         IF CT(I) = 89 THEN NOCT = NOCT + 1: NICT = NICT + 3: GOTO NEXTCTU
         IF CT(I) = 165 THEN NOCT = NOCT + 2: NICT = NICT + 2: GOTO NEXTCTU
         IF CT(I) = 101 THEN NOCT = NOCT + 1: NICT = NICT + 3: GOTO NEXTCTU
         IF CT(I) = 149 THEN NOCT = NOCT + 1: NICT = NICT + 3: GOTO NEXTCTU
         IF CT(I) = 85 THEN NICT = NICT + 4: GOTO NEXTCTU
         PRINT " **ERROR**INVALID CT("; I; ") = "; CT(I); " OR CT POSITIONING"
NEXTCTU:
      NEXT I

   REM**CONVERT I/O CARD COUNTS TO PORT COUNTS
      IF NDP$ = "N" THEN NOCT = NOCT * 3: NICT = NICT * 3
      IF NDP$ = "X" THEN NOCT = NOCT * 4: NICT = NICT * 4
       
   REM**CHECK IF PORT COUNTS EQUAL NUMBER OF PORTS INPUTTED
      IF NOCT <> NO THEN
        PRINT "**ERROR**NUMBER OF OUTPUT PORTS COUNTED IN CT NOT EQUAL TO NO"
        INTERR = 1
      END IF

      IF NICT <> NI THEN
        PRINT "**ERROR**NUMBER OF INPUT PORTS COUNTED IN CT NOT EQUAL TO NI"
        INTERR = 1
      END IF
 
INCHKCMP:
   REM*********INITIALIZATION PARAMETER CHECKING IS COMPLETE**********
   REM**SET UP UART IN PC
      OUT PA + 3, 128       'Turn on bit 7 of UART's line control...
                            '...register (LCR) to access baud rate
      OUT PA, BAUDLS        'Set LS latch for desired baud rate
      OUT PA + 1, 0         'Set MS latch = 0 for all in use baud rates
      OUT PA + 3, 7         'Set up UART for 8 data bits and 2 stop bits

                            'Note: including the 2 stop bits is...
                            '...recommended especially at the higher...
                            '...baud rates of 57600 and 115200. However...
                            '...if you are only using baud rates of...
                            '...28800 and below you can replace the above...
                            '...line with the following line providing 1...
                            '...stop bit that will speed up response a bit.

     'OUT PA + 3, 3         'Optional, set up UART for 8 data bits...
                            '...and 1 stop bit

  REM**DEFINE INITIALIZATION MESSAGE PARAMETERS
     MT = ASC("I")               'Define message type = "I" (decimal 73)
     OB(1) = ASC(NDP$)           'Define node definition parameter
     OB(2) = INT(DL / 256)       'Set USIC delay high-order byte
     OB(3) = DL - (OB(2) * 256)  'Set USIC delay low-order byte
     OB(4) = NS                  'Define number of card sets of 4 for...
                                 'USIC and SUSIC cases and the...
                                 '...number of 2-lead yellow aspect...
                                 '...oscillating signals for the SMINI.
     LM = 4  'Initialize length of message to start of loading CT elements

  REM**CHECK TYPE OF NODE TO CONTINUE SPECIFIC INITIALIZATION
     IF NDP$ = "M" THEN GOTO INITSMINI  'SMINI node so branch accordingly

INITUSIC:
  REM**SUSIC-NODE (either "N" or "X") SO LOAD CT( ) ARRAY ELEMENTS
     FOR I = 1 TO NS     'Loop through number of card sets...
        LM = LM + 1      '...accumulating message length while...
        OB(LM) = CT(I)   '...loading card type definition CT...
     NEXT I              '...array elements into output byte array
     GOTO TXMSG  'CT( )s complete so branch to transmit initialization...
                 '...message to interface
INITSMINI:
  REM**SMINI-NODE ("M") SO CHECK IF REQUIRES 2-LEAD OSCILLATION...
                   '...SEARCHLIGHT SIGNALS
     IF NS = 0 THEN GOTO TXMSG 'No signals so hold message length at...
                               '...LM = 4 and branch to transmit packet
                                     
  REM**SMINI CASE WITH SIGNALS (NS > 0) SO LOOP THROUGH TO LOAD...
     FOR I = 1 TO 6       '...signal location CT array elements...
        LM = LM + 1       '...into output byte array while...
        OB(LM) = CT(I)    '...accumulating message length
     NEXT I

  REM**FORM INITIALIZATION PACKET AND TRANSMIT TO INTERFACE
TXMSG: CALL TXPACK      'Invoke transmit packet subroutine
             
REM**COMPLETED USE OF OUTPUT BYTE ARRAY SO CLEAR IT BEFORE EXIT SUBROUTINE
     FOR I = 1 TO NO: OB(I) = 0: NEXT I
INITRET:        'Return to application program
END SUB

SUB INITRR
REM GLOBAL PARAMETERS TO THE SYSTEM
   COMPORT = 1      'PC COM PORT = 1, 2, 3 or 4
   BAUD100 = 96     'BAUD RATE OF 9600 DIVIDED BY 100
   DL = 0           'USIC TRANSMISSION DELAY
   MAXTRIES = 10000 'MAXIMUM READ TRIES BEFORE ABORT INPUTS

REM INITIALIZE SUSIC #1
   UA = 16          'USIC NODE ADDRESS
   NDP$ = "X"       'NODE DEFINITION PARAMETER SUSIC
   NS = 2           'NUMBER OF CARD SETS OF 4
   CT(1) = 153      'CARD SET IS IOIO
   CT(2) = 153      'CARD SET IS IOIO
   NI = 16          'NUMBER OF INPUT PORTS
   NO = 16          'NUMBER OF OUTPUT PORTS
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SUSIC

REM INITALIZE SMINI #1  Walton
   UA = 1           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 1           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   'CT(1) = 0: CT(2) = 0: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

REM INITALIZE SMINI #2   Sparta
   UA = 2           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 0           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   'CT(1) = 0: CT(2) = 0: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

REM INITALIZE SMINI #3   Worthville
   UA = 3           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 4           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   CT(1) = 0: CT(2) = 255: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

REM INITALIZE SMINI #4   Worthville
   UA = 4           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 0           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   CT(1) = 0: CT(2) = 0: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

REM INITALIZE SMINI #5   N Latomia
   UA = 5           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 0           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   CT(1) = 0: CT(2) = 0: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

REM INITALIZE SMINI #6   S Latonia
   UA = 6           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 0           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   CT(1) = 0: CT(2) = 0: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

REM INITALIZE SMINI #7   N Campbellsburg
   UA = 7           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 0           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   CT(1) = 0: CT(2) = 0: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

REM INITALIZE SMINI #8   S Campbellsburg
   UA = 8           'SMINI NODE ADDRESS
   NDP$ = "M"       'NODE DEFINITION PARAMETER
   NS = 0           'NUMBER OF 2-LEAD SEARCHLIGHT SIGNALS
   NI = 3           'NUMBER OF INPUT PORTS
   NO = 6           'NUMBER OF OUTPUT PORTS
   CT(1) = 0: CT(2) = 0: CT(3) = 0: CT(4) = 0: CT(5) = 0: CT(6) = 0
   ' line above for search light signal definitions
   CALL INIT        'INVOKE INITIALIZATION SUBROUTINE FOR SMINI

   CALL HEADER
       LOCATE 6, 25: PRINT "COMPUTER MODEL RAILROAD INTERFACE"
       LOCATE 7, 25: PRINT "NODE INITIALIZATION IS COMPLETE"
       LOCATE 8, 25: PRINT "CHECK GREEN STATUS LED BLINK RATE"
       LOCATE 9, 25: PRINT "1 second ON, 1 second OFF"

DO
LOOP WHILE INKEY$ = ""


' Get Fast Clock Start Time and Ratio
Filenum% = FREEFILE
File$ = "FASTCLK.DAT"
OPEN File$ FOR INPUT AS FREEFILE
INPUT #Filenum%, Ratio, Hours, Mins
CLOSE #Filenum%

265
CALL HEADER
LOCATE 17, 52: PRINT "START "; : PRINT USING "##"; Hours; : PRINT ":"; : PRINT USING "##"; Mins;
LOCATE 17, 69: PRINT "RATIO "; : PRINT USING "#"; Ratio; : PRINT ":1"

LOCATE 11, 37: PRINT "MENUE"
LOCATE 13, 30: PRINT "1) Speed Match Locos"
LOCATE 14, 30: PRINT "2) Test Outputs"
LOCATE 15, 30: PRINT "3) Test SMINI boards"
LOCATE 16, 30: PRINT "4) Test Signals "
LOCATE 17, 30: PRINT "5) Set Fast Clock"
LOCATE 18, 30: PRINT "9) Start C/MRI"
LOCATE 19, 30: PRINT "0) QUIT"

270 Inpt$ = INKEY$

Inpt$ = UCASE$(Inpt$)
IF Inpt$ = "1" THEN CALL SPEEDTEST
IF Inpt$ = "2" THEN CALL TESTOUTPUTS
IF Inpt$ = "3" THEN CALL SMINItest
IF Inpt$ = "4" THEN CALL TestSignals
IF Inpt$ = "5" THEN CALL FastClk
IF Inpt$ = "9" THEN GOTO 348
IF Inpt$ = "0" THEN CLS : END


IF Inpt$ = "" GOTO 270

GOTO 265
PLAY "MB O3 L16 A D": LOCATE 16, 45: PRINT "Not Implemented Yet"

348 LOCATE 19, 25: PRINT "Display Status? (Y), Display I/O? (I), Test? (T)       ";
350 Inpt$ = INKEY$
IF Inpt$ = "" GOTO 350
Diagnose$ = UCASE$(Inpt$)

    LOCATE 20, 25: PRINT "Signals approach lit (Y/N)?                      ";
351 Inpt$ = INKEY$
IF Inpt$ = "" GOTO 351
Signal$ = UCASE$(Inpt$)

END SUB

SUB INPUTS
  REM******************************************************
  REM**                ***INPUTS***                      **
  REM**************QB4.5 CALL VERSION**********************
  REM** SUBROUTINE TO READ INPUT BYTES IB(1) THRU IB(NI) **
  REM**    for use with USIC, SUSIC and SMINI nodes      **
  REM******************************************************
  REM**TRANSMIT POLL REQUEST TO INITIATE RECEIVING DATA BACK FROM...
                     '...INTERFACE HARDWARE
REPOL:
      MT = ASC("P")  'Define message type as poll request "P" (decimal 80)
      CALL TXPACK    'Invoke transmit packet subroutine to transmit...
                     '  ...poll request message to external hardware

  REM**LOOP ON RECEIVING INPUT BYTES UNTIL RECEIVE A Start-of-Text (STX)
GETSTX:
     CALL RXBYTE                       'Receive input byte
     IF ABORTIN = 1 THEN GOTO INPUTRET
     IF INBYTE <> 2 THEN GOTO GETSTX   'input byte not STX so branch...
                                       '...back to read another byte

  REM**RECEIVED STX SO READ NEXT BYTE AND SEE IF RETURNED DATA IS...
                      '...COMING FROM THE CORRECT USIC ADDRESS
     CALL RXBYTE      'Receive input byte which should be USIC address
     IF ABORTIN = 1 THEN GOTO INPUTRET
     INBYTE = INBYTE - 65 'Subtract offset of 65 from address and...
                          '...check that matches node that was polled
     IF INBYTE <> UA THEN PRINT "ERROR; Received bad UA = "; IB: GOTO REPOL

  REM**CORRECT UA IS REPLYING BACK TO PC SO CHECK IF "R" MESSAGE
     CALL RXBYTE          'Receive input byte which shoud be "R" (decimal 82)
     IF ABORTIN = 1 THEN GOTO INPUTRET
     IF INBYTE <> 82 THEN PRINT "Error received not = R for UA = "; UA: GOTO REPOL

  REM**MESSAGE IS "R" SO LOOP THROUGH READING INPUTS FROM INPUT PORTS...
                          '...ON INTERFACE HARDWARE
     FOR I = 1 TO NI    'Loop through number of input ports
        CALL RXBYTE     'Receive input byte
        IF ABORTIN = 1 THEN GOTO INPUTRET
    IF INBYTE = 2 THEN LOCATE 5, 1: PRINT "ERROR: No DLE ahead of 2 for UA = "; UA: GOTO REPOL
    IF INBYTE = 3 THEN LOCATE 6, 1: PRINT "ERROR: No DLE ahead of 3 for UA = "; UA: GOTO REPOL
        IF INBYTE = 16 THEN CALL RXBYTE    'DLE so read next byte and...
        IB(I) = INBYTE                     '...store as valid input byte
     NEXT I

  REM**RECEIVED ALL NI INPUT BYTES SO CHECK FOR End-of-Text (ETX = 3)
     CALL RXBYTE     'Receive input byte which should be ETX
     IF ABORTIN = 1 THEN GOTO INPUTRET
     IF INBYTE <> 3 THEN LOCATE 19, 1: PRINT "ERROR: End-of-Text ETX NOT PROPERLY RECEIVED FOR UA = "; UA; : PRINT "INPUT BYTE ="; : PRINT INBYTE

INPUTRET:       'Receive message complete so execute return
                'Note: if aborted inputs then ABORTIN = 1 else = 0
END SUB

SUB OUTPUTS
  REM********************************************************
  REM**                ***OUTPUTS***                       **
  REM******************QB4.5 CALL VERSION********************
  REM** SUBROUTINE TO WRITE OUTPUT BYTES OB(1) THRU OB(NO) **
  REM**     for use with USIC, SUSIC and SMINI nodes       **
  REM********************************************************
  REM**TRANSMIT DATA FROM PC TO OUTPUT PORTS ON INTERFACE HARDWARE
     MT = ASC("T")  'Define message type = "T" (decimal 84)
     LM = NO        'Define message length as number of output ports
     CALL TXPACK    'Invoke transmit packet subroutine
                    'Transmit message complete so return to calling program
END SUB

SUB READRR

REM**READ INPUT BYTES FROM SMINI #1, 3 INPUT PORTS at Walton
 UA = 1: NI = 3: 'CARD 1, 3 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN
  IF Diagnose$ = "I" THEN
   LOCATE 10, 1: PRINT "SMINI #1 INPUT BYTES =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3);
  END IF
REM UNPACK INPUT BYTES
     SWITCHREV(53) = IB(1) \ B0 AND W1    'NODE 1 PORT A
     SWITCHREV(51) = IB(1) \ B1 AND W1
     SWITCHREV(49) = IB(1) \ B2 AND W1
     SWITCHREV(47) = IB(1) \ B3 AND W1
     SMFBN(53) = IB(1) \ B4 AND W1
     SMFBN(51) = IB(1) \ B5 AND W1
     SMFBN(49) = IB(1) \ B6 AND W1
     SMFBN(47) = IB(1) \ B7 AND W1

     KEYSWITCH(53) = IB(2) \ B0 AND W1    'NODE 1 PORT B
     KEYSWITCH(51) = IB(2) \ B1 AND W1
     KEYSWITCH(49) = IB(2) \ B2 AND W1
     KEYSWITCH(47) = IB(2) \ B3 AND W1
     BLK(25) = IB(2) \ B4 AND W1
     BLK(26) = IB(2) \ B5 AND W1
     BLK(27) = IB(2) \ B6 AND W1
     BLK(28) = IB(2) \ B7 AND W1

     BLK(29) = IB(3) \ B0 AND W1     'NODE 1 PORT C
     BLK(30) = IB(3) \ B1 AND W1
     BLK(31) = IB(3) \ B2 AND W1
     BLK(32) = IB(3) \ B3 AND W1
     BLK(33) = IB(3) \ B4 AND W1
     SMFBN(37) = IB(3) \ B5 AND W1    ' WORTHVILLE SW 37
     KEYSWITCH(37) = IB(3) \ B6 AND W1
     SWITCHREV(37) = IB(3) \ B7 AND W1

REM**READ INPUT BYTES FROM SMINI #1, 3 INPUT PORTS at Sparta
 UA = 2: NI = 3: 'CARD 1, 3 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN
  IF Diagnose$ = "I" THEN
   LOCATE 11, 1: PRINT "SMINI #2 INPUT BYTES =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3);
  END IF
REM UNPACK INPUT BYTES
     BLK(37) = IB(1) \ B0 AND W1    'NODE 2 PORT A
     BLK(38) = IB(1) \ B1 AND W1
     BLK(39) = IB(1) \ B2 AND W1
     BLK(40) = IB(1) \ B3 AND W1
     BLK(41) = IB(1) \ B4 AND W1
     BLK(42) = IB(1) \ B5 AND W1
     BLK(43) = IB(1) \ B6 AND W1
     BLK(44) = IB(1) \ B7 AND W1

     BLK(45) = IB(2) \ B0 AND W1    'NODE 2 PORT B
     BLK(46) = IB(2) \ B1 AND W1
     BLK(47) = IB(2) \ B2 AND W1
     BLK(48) = IB(2) \ B3 AND W1
     SMFBN(45) = IB(2) \ B4 AND W1
     SMFBN(43) = IB(2) \ B5 AND W1
     SMFBN(41) = IB(2) \ B6 AND W1
     SMFBN(39) = IB(2) \ B7 AND W1

     SWITCHREV(45) = IB(3) \ B0 AND W1     'NODE 2 PORT C
     SWITCHREV(43) = IB(3) \ B1 AND W1
     SWITCHREV(41) = IB(3) \ B2 AND W1
     SWITCHREV(39) = IB(3) \ B3 AND W1
     KEYSWITCH(45) = IB(3) \ B4 AND W1
     KEYSWITCH(43) = IB(3) \ B5 AND W1
     KEYSWITCH(41) = IB(3) \ B6 AND W1
     KEYSWITCH(39) = IB(3) \ B7 AND W1

REM**READ INPUT BYTES FROM NODE 16 SUSIC 4 INPUT PORTS DeCoursey Yard
 UA = 16: NI = 16 'CARD 0, 4 INPUTS CARD 4 X 4 = 16 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3), IB(4).....
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN if you are not displaying equip status
  IF Diagnose$ = "I" THEN
   LOCATE 6, 1: PRINT "SUSIC#1  INPUT BYTES CARD 0 =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3); : PRINT USING "####"; IB(4);
   PRINT " CARD 2 =";
   PRINT USING "####"; IB(5); : PRINT USING "####"; IB(6);
   PRINT USING "####"; IB(7); : PRINT USING "####"; IB(8);
   LOCATE 7, 1: PRINT "SUSIC#1  INPUT BYTES CARD 4 =";
   PRINT USING "####"; IB(9); : PRINT USING "####"; IB(10);
   PRINT USING "####"; IB(11); : PRINT USING "####"; IB(12);
   PRINT " CARD 6 =";
   PRINT USING "####"; IB(13); : PRINT USING "####"; IB(14);
   PRINT USING "####"; IB(15); : PRINT USING "####"; IB(16);
  END IF
  
REM UNPACK INPUT BYTES
     BLK(1) = IB(1) \ B0 AND W1    'NODE 16 CARD 0 PORT A
     BLK(2) = IB(1) \ B1 AND W1
     BLK(3) = IB(1) \ B2 AND W1
     BLK(4) = IB(1) \ B3 AND W1
     BLK(5) = IB(1) \ B4 AND W1
     BLK(6) = IB(1) \ B5 AND W1
     BLK(7) = IB(1) \ B6 AND W1
     BLK(8) = IB(1) \ B7 AND W1

     BLK(9) = IB(2) \ B0 AND W1    'NODE 16 CARD 0 PORT B
     BLK(10) = IB(2) \ B1 AND W1
     BLK(11) = IB(2) \ B2 AND W1
     BLK(12) = IB(2) \ B3 AND W1
     BLK(171) = IB(2) \ B4 AND W1

     BLK(20) = IB(3) \ B7 AND W1        ' NODE 16 CARD 0 PORT C

     BLK(21) = IB(4) \ B0 AND W1        'NODE 16 CARD 0 PORT D
     BLK(22) = IB(4) \ B1 AND W1
     BLK(23) = IB(4) \ B2 AND W1
     BLK(24) = IB(4) \ B3 AND W1
     BLK(168) = IB(4) \ B4 AND W1
     BLK(169) = IB(4) \ B5 AND W1
     BLK(170) = IB(4) \ B6 AND W1

     MAINSOUTH = IB(5) \ B0 AND W1          'NODE 16 CARD 2 PORT A
     TRACKNORTH(1) = IB(5) \ B1 AND W1
     TRACKNORTH(2) = IB(5) \ B2 AND W1
     TRACKNORTH(3) = IB(5) \ B3 AND W1
     TRACKNORTH(4) = IB(5) \ B4 AND W1
     TRACKNORTH(5) = IB(5) \ B5 AND W1
     TRACKNORTH(6) = IB(5) \ B6 AND W1
     TRACKNORTH(7) = IB(5) \ B7 AND W1

     TRACKSOUTH(1) = IB(6) \ B0 AND W1          'NODE 16 CARD 2 PORT B
     TRACKSOUTH(2) = IB(6) \ B1 AND W1
     TRACKSOUTH(3) = IB(6) \ B2 AND W1
     TRACKSOUTH(4) = IB(6) \ B3 AND W1
     TRACKSOUTH(5) = IB(6) \ B4 AND W1
     TRACKSOUTH(6) = IB(6) \ B5 AND W1
     TRACKSOUTH(7) = IB(6) \ B6 AND W1
     MAINNORTH = IB(6) \ B7 AND W1

     BLK(13) = IB(7) \ B0 AND W1           'NODE 16 CARD 2 PORT C
     BLK(14) = IB(7) \ B1 AND W1
     BLK(15) = IB(7) \ B2 AND W1
     BLK(16) = IB(7) \ B3 AND W1
     BLK(17) = IB(7) \ B4 AND W1
     BLK(18) = IB(7) \ B5 AND W1
     BLK(19) = IB(7) \ B6 AND W1
     BLK(173) = IB(7) \ B7 AND W1

     SMFBN(67) = IB(8) \ B0 AND W1      'NODE 16 CARD 2 PORT D
     SMFBN(69) = IB(8) \ B1 AND W1
     SMFBN(71) = IB(8) \ B2 AND W1
   
     SWITCHN(1) = IB(9) \ B0 AND W1    'NODE 16 CARD 4 PORT A
     SWITCHREV(1) = IB(9) \ B1 AND W1
     SWITCHN(2) = IB(9) \ B2 AND W1
     SWITCHREV(2) = IB(9) \ B3 AND W1
     SWITCHN(3) = IB(9) \ B4 AND W1
     SWITCHREV(3) = IB(9) \ B5 AND W1
     KEYSWITCH(67) = IB(9) \ B6 AND W1
     SWITCHREV(67) = IB(9) \ B7 AND W1

     SMFBN(115) = IB(10) \ B0 AND W1  'NODE 16 CARD 4 PORT B
     SMFBN(116) = IB(10) \ B1 AND W1
     SMFBN(117) = IB(10) \ B2 AND W1
     SMFBN(118) = IB(10) \ B3 AND W1
     PB(0) = IB(10) \ B6 AND W1
     PB(1) = IB(10) \ B7 AND W1

     PB(2) = IB(11) \ B0 AND W1  'NODE 16 CARD 4 PORT C
     PB(3) = IB(11) \ B1 AND W1
     PB(4) = IB(11) \ B2 AND W1
     PB(5) = IB(11) \ B3 AND W1
     PB(6) = IB(11) \ B4 AND W1
     PB(7) = IB(11) \ B5 AND W1
     PB(8) = IB(11) \ B6 AND W1
     PB(9) = IB(11) \ B7 AND W1

     PB(10) = IB(12) \ B0 AND W1  'NODE 16 CARD 4 PORT D
     PB(11) = IB(12) \ B1 AND W1
     PB(12) = IB(12) \ B2 AND W1
     PB(13) = IB(12) \ B3 AND W1
     PB(14) = IB(12) \ B4 AND W1
     PB(15) = IB(12) \ B5 AND W1
     PB(16) = IB(12) \ B6 AND W1
     PB(17) = IB(12) \ B7 AND W1





    ' SWITCHN(4) = IB(13) \ B0 AND W1    'NODE 16 CARD 6 PORT A
    ' PB(18) = IB(13) \ B2 AND W1
    ' PB(19) = IB(13) \ B3 AND W1
    ' PB(20) = IB(13) \ B4 AND W1
    ' PB(21) = IB(13) \ B5 AND W1
    ' SMFBT(5) = IB(13) \ B6 AND W1: 'EK TRACK 5
    ' SMFBT(4) = IB(13) \ B7 AND W1: 'EK TRACK 4

    ' SMFBT(3) = IB(14) \ B0 AND W1     'NODE 0 CARD 6 PORT B
    ' SMFBT(2) = IB(14) \ B1 AND W1:  'EK TRACK 2
    ' SMFBT(1) = IB(14) \ B2 AND W1:  'EK TRACK 1
    '
     'SWITCHN(1) = IB(15) \ B0 AND W1    'NODE 0 CARD 6 PORT C
     'SWITCHREV(1) = IB(15) \ B1 AND W1
     'SWITCHN(2) = IB(15) \ B2 AND W1
     'SWITCHREV(2) = IB(15) \ B3 AND W1
     'SWITCHN(3) = IB(15) \ B4 AND W1
     'SWITCHREV(3) = IB(15) \ B5 AND W1
     '= IB(15) \ B6 AND W1
     '= IB(15) \ B7 AND W1

     '= IB(16) \ B0 AND W1     'NODE 0 CARD 6 PORT D
     
REM**READ INPUT BYTES FROM SMINI #3, 3 INPUT PORTS at Worthville
 UA = 3: NI = 3: 'CARD 3, 3 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN
  IF Diagnose$ = "I" THEN
   LOCATE 12, 1: PRINT "SMINI #3 INPUT BYTES =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3);
  END IF
REM UNPACK INPUT BYTES
     BLK(49) = IB(1) \ B0 AND W1    'NODE 3 PORT A
     BLK(50) = IB(1) \ B1 AND W1
     BLK(51) = IB(1) \ B2 AND W1
     BLK(52) = IB(1) \ B3 AND W1
     BLK(53) = IB(1) \ B4 AND W1
     BLK(54) = IB(1) \ B5 AND W1
     BLK(55) = IB(1) \ B6 AND W1
     BLK(56) = IB(1) \ B7 AND W1

     BLK(57) = IB(2) \ B0 AND W1    'NODE 3 PORT B
     BLK(58) = IB(2) \ B1 AND W1
     BLK(59) = IB(2) \ B2 AND W1
     BLK(60) = IB(2) \ B3 AND W1
     SMFBN(35) = IB(2) \ B4 AND W1
     KEYSWITCH(35) = IB(2) \ B5 AND W1
     SWITCHREV(35) = IB(2) \ B6 AND W1
     SMFBN(33) = IB(2) \ B7 AND W1

     KEYSWITCH(33) = IB(3) \ B0 AND W1     'NODE 3 PORT C
     SWITCHREV(33) = IB(3) \ B1 AND W1
     SMFBN(31) = IB(3) \ B2 AND W1
     KEYSWITCH(31) = IB(3) \ B3 AND W1
     SWITCHREV(31) = IB(3) \ B4 AND W1
     SMFBN(29) = IB(3) \ B5 AND W1
     KEYSWITCH(29) = IB(3) \ B6 AND W1
     SWITCHREV(29) = IB(3) \ B7 AND W1

REM**READ INPUT BYTES FROM SMINI #4, 3 INPUT PORTS at Worthville
 UA = 4: NI = 3: 'CARD 4, 3 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN
  IF Diagnose$ = "I" THEN
   LOCATE 13, 1: PRINT "SMINI #4 INPUT BYTES =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3);
  END IF
REM UNPACK INPUT BYTES
     ' = IB(1) \ B0 AND W1    'NODE 4 PORT A
     ' = IB(1) \ B1 AND W1
     ' = IB(1) \ B2 AND W1
     ' = IB(1) \ B3 AND W1
     ' = IB(1) \ B4 AND W1
     ' = IB(1) \ B5 AND W1
     ' = IB(1) \ B6 AND W1
     ' = IB(1) \ B7 AND W1

     ' = IB(2) \ B0 AND W1    'NODE 4 PORT B
     ' = IB(2) \ B1 AND W1
     ' = IB(2) \ B2 AND W1
     ' = IB(2) \ B3 AND W1
     ' = IB(2) \ B4 AND W1
     ' = IB(2) \ B5 AND W1
     ' = IB(2) \ B6 AND W1
     BLK(69) = IB(2) \ B7 AND W1

     BLK(61) = IB(3) \ B0 AND W1     'NODE 4 PORT C
     BLK(62) = IB(3) \ B1 AND W1
     BLK(63) = IB(3) \ B2 AND W1
     BLK(64) = IB(3) \ B3 AND W1
     BLK(65) = IB(3) \ B4 AND W1
     BLK(66) = IB(3) \ B5 AND W1
     BLK(67) = IB(3) \ B6 AND W1
     BLK(68) = IB(3) \ B7 AND W1

REM**READ INPUT BYTES FROM SMINI #5, 3 INPUT PORTS at N Latonia
 UA = 5: NI = 3: 'CARD 6, 3 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN
  IF Diagnose$ = "I" THEN
   LOCATE 14, 1: PRINT "SMINI #5 INPUT BYTES =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3);
  END IF
REM UNPACK INPUT BYTES
     PB(22) = IB(1) \ B0 AND W1    'NODE 5 PORT A
     PB(23) = IB(1) \ B1 AND W1
     PB(24) = IB(1) \ B2 AND W1
     PB(25) = IB(1) \ B3 AND W1
     PB(26) = IB(1) \ B4 AND W1
     PB(27) = IB(1) \ B5 AND W1
     PB(28) = IB(1) \ B6 AND W1
     PB(29) = IB(1) \ B7 AND W1

     PB(30) = IB(2) \ B0 AND W1     'NODE 5 PORT B
     PB(31) = IB(2) \ B1 AND W1
     PB(32) = IB(2) \ B2 AND W1
     PB(33) = IB(2) \ B3 AND W1
     PB(34) = IB(2) \ B4 AND W1
     PB(35) = IB(2) \ B5 AND W1
     PB(36) = IB(2) \ B6 AND W1
     SWITCHREV(55) = IB(2) \ B7 AND W1

     SMFBN(65) = IB(3) \ B0 AND W1: ' DRILL   NODE 5 PORT C
     SMFBN(63) = IB(3) \ B1 AND W1: ' A/D
     SMFBN(59) = IB(3) \ B2 AND W1: ' CROSSOVER
     KEYSWITCH(59) = IB(3) \ B3 AND W1
     SWITCHREV(59) = IB(3) \ B4 AND W1
     KEYSWITCH(61) = IB(3) \ B5 AND W1
     SMFBN(61) = IB(3) \ B6 AND W1
     SMFBR(61) = IB(3) \ B7 AND W1: 'Lock SW(59)

REM**READ INPUT BYTES FROM SMINI #6, 3 INPUT PORTS at S Latonia
 UA = 6: NI = 3: 'SMINI 6, 3 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN
  IF Diagnose$ = "I" THEN
   LOCATE 15, 1: PRINT "SMINI #6 INPUT BYTES =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3);
  END IF
REM UNPACK INPUT BYTES
     SMFBN(57) = IB(1) \ B0 AND W1: ' SW SIDING  'NODE 6 PORT A
     SMFBN(55) = IB(1) \ B1 AND W1: ' SW MAIN
     SMFBN(17) = IB(1) \ B2 AND W1
     KEYSWITCH(17) = IB(1) \ B3 AND W1
     SWITCHREV(17) = IB(1) \ B4 AND W1
     SMFBN(19) = IB(1) \ B5 AND W1
     KEYSWITCH(19) = IB(1) \ B6 AND W1
     SWITCHREV(19) = IB(1) \ B7 AND W1

     SMFBN(21) = IB(2) \ B0 AND W1: '     NODE 6 PORT B
     KEYSWITCH(21) = IB(2) \ B1 AND W1
     SWITCHREV(21) = IB(2) \ B2 AND W1

REM**READ INPUT BYTES FROM SMINI #7, 3 INPUT PORTS at N Campbellsburg
 UA = 7: NI = 3: 'SMINI 7, 3 INPUTS
 CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
REM**DISPLAY INPUT BYTES ON MONITOR SCREEN
  IF Diagnose$ = "I" THEN
   LOCATE 16, 1: PRINT "SMINI #7 INPUT BYTES =";
   PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2);
   PRINT USING "####"; IB(3);
  END IF
REM UNPACK INPUT BYTES
     BLK(73) = IB(1) \ B0 AND W1     'NODE 7 PORT A
     BLK(74) = IB(1) \ B1 AND W1
     BLK(75) = IB(1) \ B2 AND W1
     BLK(76) = IB(1) \ B3 AND W1
     BLK(77) = IB(1) \ B4 AND W1
     BLK(78) = IB(1) \ B5 AND W1
     BLK(79) = IB(1) \ B6 AND W1
     BLK(80) = IB(1) \ B7 AND W1

     BLK(81) = IB(2) \ B0 AND W1     'NODE 7 PORT B
     BLK(82) = IB(2) \ B1 AND W1
     BLK(83) = IB(2) \ B2 AND W1
     BLK(84) = IB(2) \ B3 AND W1
     SMFBN(27) = IB(2) \ B4 AND W1
     KEYSWITCH(27) = IB(2) \ B5 AND W1
     SWITCHREV(27) = IB(2) \ B6 AND W1
     SMFBN(25) = IB(2) \ B7 AND W1

     KEYSWITCH(25) = IB(3) \ B0 AND W1  'NODE 7 PORT C
     SWITCHREV(25) = IB(3) \ B1 AND W1
     SMFBN(23) = IB(3) \ B2 AND W1
     KEYSWITCH(23) = IB(3) \ B3 AND W1
     SWITCHREV(23) = IB(3) \ B4 AND W1




END SUB

SUB RXBYTE
  REM************************************************
  REM**               ***RXBYTE***                 **
  REM*************QB4.5 CALL VERSION*****************
  REM** SUBROUTINE TO RECEIVE BYTE AT PC FROM NODE **
  REM**  for use with USIC, SUSIC and SMINI nodes  **
  REM************************************************
  REM**Note: Reference page 41 of Serial Port Complete book for...
  REM**...more detailed definition and usage of line control...
  REM**...register (LCR) and line status register (LSR) as...
  REM**...applicable to standard 8250, 15450 and 16550 UARTs.

  REM**INITIALIZE INPUT TRIES COUNTER AND ABORTING INPUT FLAG
     INTRIES = 0  'Initialize input tries counter to 0
     ABORTIN = 0  'Initialize aborting input flag to 0

  REM**SET UP A MAJOR LOOP STARTING AT INLOOP FOR PC TO RECEIVE AN...
              '...INPUT BYTE FROM THE INTERFACE HARDWARE
  REM**START LOOP BY CHECKING FOR PC OVERRUN ERROR
INLOOP:
     LSR = INP(PA + 5)         'Read UART's line status register (LSR)...

     IF (LSR AND 2) <> 0 THEN  '...and if bit 1 set, PC has overrun...
                               '...error, so print error message
       PRINT "PC overrun at node = "; UA; "line status register = "; LSR
     END IF

  REM**CHECK IF INPUT TRIES EXCEED MAXIMUM ALLOWED
     INTRIES = INTRIES + 1       'Increment input tries counter
     IF INTRIES > MAXTRIES THEN  'If counter exceeds maximum tries...
                                 '    ...then abort reading inputs
       ABORTIN = 1:  INTRIES = 0
       LOCATE 1, 1: PRINT "INPUT TRIES EXCEEDED = "; MAXTRIES; "  NODE = "; UA; "ABORTING INPUT"
       INBYTE = 0   'Aborted input so set input byte value to 0...
       GOTO RXRET   '...and branch to receive input byte return
     END IF

  REM**READING INPUTS NOT ABORTED SO CHECK PC LINE STATUS REGISTER...
                         '...TO SEE IF INPUT BUFFER IS LOADED
     LSR = INP(PA + 5)   'Read UART's line status register (LSR) and...
     IF (LSR AND 1) = 0 THEN GOTO INLOOP  '...if input buffer not...
                           '...yet loaded (bit 0 in LSR is clear)...
                           '...then branch back to beginning of...
                           '...input loop to try read again

  REM**PC SERIAL INPUT BUFFER IS LOADED SO RECEIVED INPUT BYTE
     INBYTE = INP(PA)  'Transfer received input byte available from COM...
                       '...port address (PA) to input byte working register

     'PRINT INBYTE   '!!!!Optional printout of input byte for test and debug
                     'Note: Invoking this print slows PC...
                     '...significantly so will most likely need...
                     '...to significantly increase USIC delay (DL)

RXRET:    'Received byte complete so return to calling program
END SUB

SUB SGCCS (NXA, SXA, X, XS, TD, PGCC)
REM ************* Standard Grade Crossing Subroutine **************
REM ** Receives occupancy status of a[[roach section & crossing  **
REM ** island and calculates the corresponding control variables **
REM ** used to activate the PGCC card. Subroutine assumes using a *
REM ** single stick but with seperatly detected approach sections *
REM ** and no approach section time out.                         **
REM ***************************************************************
REM * Initalize crossing to clear
 PGCC = CLR
REM set crossing approachequal to occupancy status or approach sections
 XA = NXA OR SXA

        IF XA = 0 THEN
         TD = 0
        ELSE
         IF TD > 0 GOTO CXX1
         IF TD = 0 THEN TD = 45
         IF TD < 0 THEN XS = 1
        END IF
CXX1:

REM If island is occupied and crossing approach is occupied then set stick occupied
 IF (X > 0 AND XA > 0) THEN XS = 1
REM If(crossing approach occupied and stick clear) or island occupied activate
 IF ((XA > 0 AND XS = 0) OR X > 0) THEN PGCC = 1
REM If crossing approach and island both clear then clear stick
 IF (X = 0 AND XA = 0) THEN XS = 0: TD = 0


REM processing complete return controll to calling program

END SUB

SUB SMINItest

DIM PND$(12)
 PND$(1) = "A": PND$(2) = "B": PND$(3) = "C":
 PND$(4) = "D": PND$(5) = "E": PND$(6) = "F"
 
CLS
LOCATE 1, 34: PRINT "TESTING SMINI"
LOCATE 3, 34: PRINT "SMINI Address    "

LOCATE 3, 47
805 INPUT ; ""; UA
 IF UA < 0 OR UA > 20 GOTO 805
NO = 6: NI = 3: 'CARD UA, 6 OUTPUTS & 3 INPUTS
Delay! = .2

REM *******BEGIN TEST LOOP*******SMINI #1
 LOCATE 23, 27
 PRINT "Press [ESC] to stop testing"

FOR J = 1 TO 5
       LOCATE 15, 52: : PRINT "Pass # "; : PRINT J
       LOCATE 15, 63: PRINT "Delay "; : PRINT USING "#.##"; Delay!
     REM**INITIALIZE LEDS TO OFF
       FOR I = 1 TO 3
        OB(I) = 0
       NEXT I
     'CALL OUTPUTS: Delay! = 1!: GOSUB 890
     
     REM**OUTPUT PORT TO BE TESTED IN A LOOP**
       
       FOR PN = 1 TO 3

     REM**INCREMENT DISPLAYED BIT NUMBER IN A LOOP
       FOR N = 0 TO 7

     REM**OUTPUT TEST STATUS TO MONITOR
       LOCATE 15, 25: PRINT "PORT = "; PND$(PN); " BIT NUMBER = "; N

     REM**SET UP TEST LED PATTERN
       OB(PN) = 2 ^ N    'Number 2 raised to power N
            LOCATE 22, 1: PRINT "SMINI#"; : PRINT USING "##"; UA; : PRINT " OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
            
     REM**OUTPUT LED DISPLAY DATA TO SMINI
       CALL OUTPUTS

     REM**DELAY LOOP SO THAT YOU CAN OBSERVE LED STATUS
       GOSUB 890
          REM *** ESCAPE KEY TRAP
          IF INKEY$ = CHR$(27) THEN GOTO 1000

        REM**COMPLETE BIT POSITION LOOP
          
       NEXT N

     REM**TURN OFF CURRENT PORT BEFORE INCREMENT TO THE NEXT PORT
       OB(PN) = 0
     REM**INCREMENT TO NEXT PORT
       NEXT PN

     REM reduce time delay
       Delay! = Delay! - .05

  NEXT J


    REM TURN ON ALL SMINI LEDS
        OB(1) = 255: OB(2) = 255: OB(3) = 255
            
            LOCATE 22, 1: PRINT "SMINI#"; : PRINT USING "##"; UA; : PRINT " OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
            

        CALL OUTPUTS: Delay! = 5!: GOSUB 890

   REM TURN OFF ALL SMINI LEDS
       OB(1) = 0: OB(2) = 0: OB(3) = 0
            LOCATE 22, 1: PRINT "SMINI#"; : PRINT USING "##"; UA; : PRINT " OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
            
            
       CALL OUTPUTS: Delay! = .5: GOSUB 890

' some code here to trigger continuation of the test, either read an input port or press any key to continue

     '  CALL INPUTS
       

        LOCATE 15, 25: PRINT "Press any key to continue test.                  ";
810     Inpt$ = INKEY$
        CALL INPUTS
        IF IB(1) <> 0 OR IB(2) <> 0 OR IB(3) <> 0 GOTO 815
        IF Inpt$ = "" GOTO 810
815     LOCATE 15, 25: PRINT "                               "

Delay! = .2
FOR J = 1 TO 5
       LOCATE 15, 52: : PRINT "Pass # "; : PRINT J
       LOCATE 15, 63: PRINT "Delay "; : PRINT USING "#.##"; Delay!

     REM**OUTPUT PORT TO BE TESTED IN A LOOP**
       FOR PN = 4 TO 6

     REM**INCREMENT DISPLAYED BIT NUMBER IN A LOOP
       FOR N = 0 TO 7

     REM**OUTPUT TEST STATUS TO MONITOR
       LOCATE 15, 25: PRINT "PORT = "; PND$(PN); " BIT NUMBER = "; N


     REM**SET UP TEST LED PATTERN
       OB(PN) = 2 ^ N    'Number 2 raised to power N
            LOCATE 22, 1: PRINT "SMINI#"; : PRINT USING "##"; UA; : PRINT " OUTPUT BYTES =";
            PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
     REM**OUTPUT LED DISPLAY DATA TO SMINI
       CALL OUTPUTS

     REM**DELAY LOOP SO CAN OBSERVE LED STATUS
       GOSUB 890

          REM *** ESCAPE KEY TRAP
          IF INKEY$ = CHR$(27) THEN GOTO 1000

       REM**COMPLETE BIT POSITION LOOP
       NEXT N

     REM**TURN OFF CURRENT PORT BEFORE INCREMENT TO THE NEXT PORT
       OB(PN) = 0
     REM**INCREMENT TO NEXT PORT
       NEXT PN

     REM reduce time delay
       Delay! = Delay! - .05

     LOCATE 23, 27

NEXT J


    REM TURN ON ALL SMINI LEDS
        OB(4) = 255: OB(5) = 255: OB(6) = 255
            LOCATE 22, 1: PRINT "SMINI#"; : PRINT USING "##"; UA; : PRINT " OUTPUT BYTES =";
            PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);

        CALL OUTPUTS: Delay! = 5!: GOSUB 890

   REM TURN OFF ALL SMINI LEDS
       OB(4) = 0:  OB(5) = 0: OB(6) = 0
            LOCATE 22, 1: PRINT "SMINI#"; : PRINT USING "##"; UA; : PRINT " OUTPUT BYTES =";
            PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);

       CALL OUTPUTS: Delay! = .5: GOSUB 890
              
        LOCATE 11, 25: PRINT "SMINI"; : PRINT USING "##"; UA; : PRINT " OUTPUT TEST COMPLETE!           "
        LOCATE 13, 25: PRINT "                                            "
        LOCATE 15, 25: PRINT "Press any key to continue test.                  ";
820     Inpt$ = INKEY$
        CALL INPUTS
        IF IB(1) = 1 THEN GOTO 840
     LOCATE 23, 27
     PRINT "Press [ESC] to stop testing"
     IF INKEY$ = CHR$(27) THEN GOTO 1000

        IF Inpt$ = "" GOTO 820
        LOCATE 15, 25: PRINT "Testing SMINI"; : PRINT USING "##"; UA; : PRINT " Inputs                         "

840   LOCATE 22, 1: PRINT "SMINI#"; : PRINT USING "##"; UA; : PRINT " INPUT BYTES = ";
850   CALL INPUTS  'Input bytes are stored as IB(1), IB(2), IB(3)
      OB(1) = IB(1): OB(2) = IB(2): OB(3) = IB(3)
      OB(4) = IB(1): OB(5) = IB(2): OB(6) = IB(3)
       
      LOCATE 22, 24: PRINT USING "####"; IB(1); : PRINT USING "####"; IB(2); : PRINT USING "####"; IB(3);

      CALL OUTPUTS
      IF IB(1) = 1 AND IB(3) = 128 THEN GOTO 1000
     LOCATE 23, 27
     PRINT "Press [ESC] to stop testing"
     IF INKEY$ = CHR$(27) THEN GOTO 1000


      GOTO 850


890   REM **Real Time Delay loop variable DELAY! is the min time delay
       Start! = TIMER
900    Finish! = TIMER
       IF Finish! - Start! < Delay! GOTO 900
      RETURN
1000



END SUB

SUB SPEEDTEST
DIM LTST!(5)
DIM Speed!(5): ' Lap Speed(I)
DIM StdD!(5)
DIM StdDev!(5): ' standard deviation

REM **** Variables for Flashing RED, Green & Yellow for signals and control panels
FRED = RED: FRED1 = DRK: FRED2 = DRK
FR = 1: FR1 = 0: FR2 = 0 'States for one color LED to flash at 1 sec on 1 sec off
FGRN = GRN: FGRN1 = DRK: FGRN2 = DRK
FYEL = YEL: FYEL1 = DRK: FYEL2 = DRK
FREDGRN = RED: FREDGRN1 = GRN: FREDGRN2 = GRN

SM(101) = TUR
SM(102) = TUR
SM(103) = TUR
SM(108) = TUR
SM(109) = TUR
SM(110) = TUR
Relay(1) = 1: ' turn on power Relay(1) to power block(4)
CALL WRITERR

500 CALL HEADER
LOCATE 3, 19
PRINT "Measuring Loco Speed On Test Loop Decoursey"
LOCATE 4, 24
PRINT "Start Loco On Loop Track #1 going anti-clockwise."
LOCATE 5, 8
PRINT "Run 5 Laps at the same speed. You will be given an average speed."
' *** set track switches to allow loop of track #1, block(4), block(2) & block(11)

LOCATE 7, 5: PRINT "Target Speed (60/45/30/15)"; : INPUT TSpeed
LOCATE 8, 5: PRINT "CV value this Speed Step from Table "; : INPUT CV
LOCATE 10.1: PRINT "READY "
' turn off all lap tracking LEDs
LED(107) = 0: LED(106) = 0: LED(105) = 0: LED(104) = 0: LED(103) = 0
' begin 5 laps (loops) to measure the elapst time and calculate speed for each lap
FOR I = 1 TO 5
' turn off LEDs that indicate progressioin around the loop
LED(115) = 0: LED(119) = O: LED(120) = 0
' Start real time loop
STRTL:
CALL READRR

' If Loco is in Block #4 (timing block), turn off LED(120) in Start block
' and start measuring elapst time by getting the start time Start!
IF BLK(4) = 0 THEN
        Start! = TIMER
       ELSE
        LED(119) = 0
        LED(120) = 0
END IF

IF BLK(4) = 1 AND BLK(11) = 1 THEN
        STST! = Start!
        LOCATE 10, 1: PRINT "TIMING"
        LED(108 - I) = GRN: ' LED(107), 106, 105, 104, 103 for Lap 1, 2, 3, 4 & 5
END IF

' On entering Block #2 time stamp end of lap, make LEDs red
IF BLK(2) = 0 THEN
        Finish! = TIMER ' until loco reaches END block keep getting a new time.
        LED(120) = 0
        LED(115) = 0
       ELSE
        LED(120) = 1
        LED(115) = RED
END IF

' On entering Block #4 time stamp the start time
' test code below
'LOCATE 7, 1: PRINT "BLK(4)"; : PRINT BLK(4); : PRINT "BLK(2)"; : PRINT BLK(2); : PRINT "Blk(11)"; : PRINT BLK(11)

IF BLK(4) = OCC AND BLK(2) = OCC THEN
        ETST! = Finish!: ' END TIME
        LOCATE 10, 1:
        PRINT "END   "
END IF
' Lap time(I) = end time - start time
IF STST! <> 0 THEN LTST!(I) = ETST! - STST!
REM lines below to debug during development
'LOCATE 8 + I, 30: PRINT Start!
'LOCATE 8 + I, 40: PRINT STST!
'LOCATE 8 + I, 50: PRINT ETST!: ' Finish Time
'LOCATE 8 + I, 60: PRINT LTST!(I)

'501 Inpt$ = INKEY$
'IF Inpt$ = "" GOTO 501

' Checking if entering aproach block before TIMING
IF BLK(11) = OCC THEN
        LED(119) = 1
        LED(115) = 0
        LED(120) = 0
       ELSE
        LED(119) = 0
END IF
IF BLK(11) = OCC AND BLK(4) = 0 THEN LOCATE 10, 1: PRINT "START "
IF BLK(4) = OCC THEN LED(119) = 0
CALL WRITERR
' Lines to debug below
'LOCATE 9 + I, 20: PRINT "Start Time"; : PRINT Start!
'LOCATE 9 + I, 40: PRINT STST!
'LOCATE 9 + I, 60: PRINT "Finish Time"; : PRINT ETST!
'LOCATE 9 + I, 80: PRINT "Lap Time"; : PRINT LTST!(I)
IF LTST!(I) > 0 THEN GOTO 505
GOTO STRTL
505 Speed!(I) = 999.182 / LTST!(I): ' distance in inches x 12"/ft x 87.1/5280 ft/mile x 3600 sec/hr
LOCATE 9 + I, 10:  PRINT " Lap Time #"; : PRINT I; : PRINT USING "###.###"; LTST!(I); : PRINT " sec.  Speed "; : PRINT USING "##.#"; Speed!(I); : PRINT " mph";
LED(108 - I) = RED
Start! = 0
Finish! = 0
STST! = 0
ETST! = 0
LTST!(I) = 0
NEXT I
' audable warning, beep each second 5 lap test is finished.
PLAY "MB O3 L16 G L8 A P2 L16 G L8 A P2 MN O0 L4 G E L2 A L4 "
'PLAY "O4 L1 A"
'PLAY "MB O3 L16 A D"
'PLAY "MF MN O0 L4 G E L2 A L4 E'"


AvgSpeed! = (Speed!(1) + Speed!(2) + Speed!(3) + Speed!(4) + Speed!(5)) / 5
StdDev! = ((((Speed!(1) - AvgSpeed!) ^ 2) + ((Speed!(2) - AvgSpeed!) ^ 2) + ((Speed!(3) - AvgSpeed!) ^ 2) + ((Speed!(4) - AvgSpeed!) ^ 2) + ((Speed!(5) - AvgSpeed!) ^ 2)) / 5) ^ .5
LOCATE 15, 5: PRINT "Std Deviation "; : PRINT USING "#.####"; StdDev!
LOCATE 15, 30: PRINT "Average Speed "; : PRINT USING "##.#"; AvgSpeed!; : PRINT " mph"

SCV! = (TSpeed / AvgSpeed!) * CV
LOCATE 8, 50: PRINT " Adj to "; : PRINT USING "###.#"; SCV!

510 Inpt$ = INKEY$
LED(107) = FRED: LED(115) = FRED: LED(119) = FR: LED(120) = FR
LED(106) = FRED: LED(105) = FRED: LED(104) = FRED: LED(103) = FRED
' Flashing LED Software
CheckTime1! = TIMER
IF CheckTime1! > CheckTime2! + 1 THEN
  CheckTime2! = TIMER
  FRED1 = FRED: FRED = FRED2: FRED2 = FRED1
  FR1 = FR: FR = FR2: FR2 = FR1
  FGRN1 = FGRN: FGRN = FGRN2: FGRN2 = FGRN1
  FYEL1 = FYEL: FYEL = FYEL2: FYLE2 = FYEL1
  FREDGRN1 = FREDGRN: FREDGRN = FREDGRN2: FREDGRN2 = FREDGRN1
END IF

CALL WRITERR

LOCATE 16, 10: PRINT "Test Another Set of 5 Laps?";

IF Inpt$ = "" GOTO 510
Inpt$ = UCASE$(Inpt$)

IF Inpt$ = "Y" THEN
       FOR I = 1 TO 5
        LTST!(I) = 0
       NEXT I
        ETST! = 0
        STST! = 0
        GOTO 500
END IF

550 CALL HEADER
Relay(1) = 0
END SUB

SUB SWLOCKS

REM *********************** DeCoursey *****************************

SWITCH67:
'SWITCH #67 CONTROLLED ELECTRIC SWITCH LOCK crossover
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(67) = 1 THEN CLL67R = 1 ELSE CLL67R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL67R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #67
    TD(67) = 0                          ' make sure any time delay is reset
    IF SMFBN(67) <> 1 THEN GOTO L67END ' if switch is not normal (reversed)
    IF KEYSWITCH(67) = 1 THEN GOTO L67END 'if key still inserted skip processing
    UL(67) = 0                           '.... lock up the switch
    LED(67) = 0                           '... and set lock indication lights to off
    GOTO L67END

'** PROCESS UNLOCK PROTOCOL #67
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(67) = 1 THEN GOTO L67END        'if already unlocked branch to end
   IF (BLK(16) OR BLK(17) = 1) THEN GOTO NOREL67     ' if switch interlock occupied go no release
   IF ((BLK(13) OR BLK(14) OR BLK(15) OR BLK(18) OR BLK(19)) = 1) THEN GOTO TIMEREL67   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL67  ' if signal on either end cleared no release
  END IF

QUICKREL67:
'*** PERFORM QUICK RELEASE
   LED(67) = 0        ' set switch lock indicator lights to off
   TD(67) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(67) = 0 THEN GOTO L67END ' if key not inserted then skip
   UL(67) = 1         ' unlock switch and ...
   LED(67) = 1        ' turn on switch unlock indicator light
   GOTO L67END

TIMEREL67:
' *** PERFORM TIME RELEASE
   LED(67) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(67) = 0 THEN TD(67) = 25     ' if timer is not set, set it to desired level
   IF TD(67) > 0 THEN GOTO L67END    ' time delay is counting, skip to end
   IF TD(67) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(67) = 0 THEN GOTO L67END      ' key not inserted... skip
      TD(67) = 0                     ' ... reset timer =0 and ...
      UL(67) = 1                     ' unlock switch
      LED(67) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L67END                      ' branch to end of processing

NOREL67:
' *** PERFORM NO RELEASE
  TD(67) = 0                      ' make sure any time delay is reset
  UL(67) = 0                      ' .... and keep switch locked
  LED(67) = 0
' lock processing complete

L67END:

      IF UL(67) = 1 THEN
        IF SWITCHREV(67) = 1 THEN SM(67) = TUR:  'Unlocked and reversed.
        IF SWITCHREV(67) = 0 THEN SM(67) = TUN   'Unlocked and normal.
      END IF


REM *********************** Latonia *******************************

SWITCH61:
'SWITCH #61 CONTROLLED MANUAL SWITCH LOCK  Newport Jct.
  IF BLK(168) = 1 THEN GOTO QUICKREL61' ASSUMES TRAIN READY TO ENTER,
  'GRANT QUICK RELEASE
  ' IF TRAIN IS IN SIDING, CREW WOULD NOT REQUEST RELEASE AS OTHER TRAIN IS IN SIGHT THERE

' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(61) = 1 THEN CLL61L = 1 ELSE CLL61L = 0  ' temp statement to release lock untill CTC is installed
  IF CLL61L = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #61
    TD(61) = 0                          ' make sure any time delay is reset
    IF SMFBN(61) <> 1 THEN GOTO L61END ' if switch ROD is not normal (reversed)
    IF KEYSWITCH(61) = 1 THEN GOTO L61END 'if key still inserted skip processing
    UL(61) = 0                           '.... lock up the switch
    IF SMFBR(61) = 1 THEN LED(61) = 0                          '... and set lock indication lights to off
    SM(61) = TUN
    GOTO L61END

'** PROCESS UNLOCK PROTOCOL #61
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(61) = 1 THEN GOTO L61END        'if already unlocked branch to end
   IF SMFBN(61) = 1 AND BLK(21) = 1 THEN GOTO NOREL61   ' if switch interlock occupied go no release
   IF SMFBN(61) = 0 AND BLK(20) = 1 THEN GOTO NOREL61   ' if switch interlock occupied go no release
   IF SMFBN(61) = 1 AND BLK(22) = 1 THEN GOTO TIMEREL61   ' if block containing switch is occupied goto time release
   IF SMFBN(61) = 0 AND BLK(23) = 1 THEN GOTO TIMEREL61   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL61  ' if signal on either end cleared no release
  END IF

QUICKREL61:
'*** PERFORM QUICK RELEASE
   LED(61) = 0        ' set switch lock indicator lights to off
   TD(61) = 0         ' make sure any time delay is reset to 0
   SM(61) = TUN       ' Lock Mechanism
   IF KEYSWITCH(61) = 0 THEN GOTO L61END ' if key not inserted then skip
   UL(61) = 1         ' unlock switch and ...
   LED(61) = 1        ' turn on switch unlock indicator light
   SM(61) = TUR       ' Release Lock Mechanism
   GOTO L61END

TIMEREL61:
' *** PERFORM TIME RELEASE
   LED(61) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(61) = 0 THEN TD(61) = 25     ' if timer is not set, set it to desired level
   IF TD(61) > 0 THEN GOTO L61END    ' time delay is counting, skip to end
   IF TD(61) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(61) = 0 THEN GOTO L61END      ' key not inserted... skip
      TD(61) = 0                     ' ... reset timer =0 and ...
      UL(61) = 1                     ' unlock switch
      LED(61) = 1                    ' turn on switch lock indicator light
      SM(61) = TUR                   ' release physical lock
    END IF
    GOTO L61END                      ' branch to end of processing

NOREL61:
' *** PERFORM NO RELEASE
  TD(61) = 0                      ' make sure any time delay is reset
  UL(61) = 0                      ' .... and keep switch locked
  LED(61) = 0
  SM(61) = TUN
' lock processing complete

L61END:

      IF UL(61) = 1 THEN SM(61) = TUR ELSE SM(61) = TUN
      ' This is the lock mechanism for a hand thrown switch.

SWITCH59:
'SWITCH #59 CONTROLLED ELECTRIC SWITCH LOCK Latonia Crossover
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(59) = 1 THEN CLL59R = 1 ELSE CLL59R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL59R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #59
    TD(59) = 0                          ' make sure any time delay is reset
    IF SMFBN(59) <> 1 THEN GOTO L59END ' if switch is not normal (reversed)
    IF KEYSWITCH(59) = 1 THEN GOTO L59END 'if key still inserted skip processing
    UL(59) = 0                           '.... lock up the switch
    LED(59) = 0                           '... and set lock indication lights to off
    GOTO L59END

'** PROCESS UNLOCK PROTOCOL #59
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(59) = 1 THEN GOTO L59END        'if already unlocked branch to end
   IF (BLK(20) OR BLK(21) = 1) THEN GOTO NOREL59     ' if switch interlock occupied go no release
   IF ((BLK(18) OR BLK(19) OR BLK(22) OR BLK(23)) = 1) THEN GOTO TIMEREL59   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL59  ' if signal on either end cleared no release
  END IF

QUICKREL59:
'*** PERFORM QUICK RELEASE
   LED(59) = 0        ' set switch lock indicator lights to off
   TD(59) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(59) = 0 THEN GOTO L59END ' if key not inserted then skip
   UL(59) = 1         ' unlock switch and ...
   LED(59) = 1        ' turn on switch unlock indicator light
   GOTO L59END

TIMEREL59:
' *** PERFORM TIME RELEASE
   LED(59) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(59) = 0 THEN TD(59) = 30     ' if timer is not set, set it to desired level
   IF TD(59) > 0 THEN GOTO L59END    ' time delay is counting, skip to end
   IF TD(59) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(59) = 0 THEN GOTO L59END      ' key not inserted... skip
      TD(59) = 0                     ' ... reset timer =0 and ...
      UL(59) = 1                     ' unlock switch
      LED(59) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L59END                      ' branch to end of processing

NOREL59:
' *** PERFORM NO RELEASE
  TD(59) = 0                      ' make sure any time delay is reset
  UL(59) = 0                      ' .... and keep switch locked
  LED(59) = 0
' lock processing complete

L59END:

      IF UL(59) = 1 THEN
        IF SWITCHREV(59) = 1 THEN SM(59) = TUR:  'Unlocked and reversed.
        IF SWITCHREV(59) = 0 THEN SM(59) = TUN   'Unlocked and normal.
      END IF


      IF BLK(25) = 0 THEN
        IF SWITCHREV(55) = 1 THEN SM(55) = TUR: ' temp statement will later be under CTC
        IF SWITCHREV(55) = 0 THEN SM(55) = TUN
      END IF



REM ********************* Walton ***************************

SWITCH53:
'SWITCH #53 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(53) = 1 THEN CLL53R = 1 ELSE CLL53R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL53R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #53
    TD(53) = 0                          ' make sure any time delay is reset
    IF SMFBN(53) <> 1 THEN GOTO L53END ' if switch is not normal (reversed)
    IF KEYSWITCH(53) = 1 THEN GOTO L53END 'if key still inserted skip processing
    UL(53) = 0                           '.... lock up the switch
    LED(53) = 0                           '... and set lock indication lights to off
    GOTO L53END

'** PROCESS UNLOCK PROTOCOL #53
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(53) = 1 THEN GOTO L53END        'if already unlocked branch to end
   IF BLK(26) = 1 THEN GOTO NOREL53      ' if switch interlock occupied go no release
   IF ((BLK(24) OR BLK(28) OR BLK(29)) = 1) THEN GOTO TIMEREL53   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL53  ' if signal on either end cleared no release
  END IF

QUICKREL53:
'*** PERFORM QUICK RELEASE
   LED(53) = 0        ' set switch lock indicator lights to off
   TD(53) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(53) = 0 THEN GOTO L53END ' if key not inserted then skip
   UL(53) = 1         ' unlock switch and ...
   LED(53) = 1        ' turn on switch unlock indicator light
   GOTO L53END

TIMEREL53:
' *** PERFORM TIME RELEASE
   LED(53) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(53) = 0 THEN TD(53) = 30     ' if timer is not set, set it to desired level
   IF TD(53) > 0 THEN GOTO L53END    ' time delay is counting, skip to end
   IF TD(53) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(53) = 0 THEN GOTO L53END      ' key not inserted... skip
      TD(53) = 0                     ' ... reset timer =0 and ...
      UL(53) = 1                     ' unlock switch
      LED(53) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L53END                      ' branch to end of processing

NOREL53:
' *** PERFORM NO RELEASE
  TD(53) = 0                      ' make sure any time delay is reset
  UL(53) = 0                      ' .... and keep switch locked
  LED(53) = 0
' lock processing complete

L53END:

      IF UL(53) = 1 THEN
        IF SWITCHREV(53) = 1 THEN SM(53) = TUR:  'Unlocked and reversed.
        IF SWITCHREV(53) = 0 THEN SM(53) = TUN   'Unlocked and normal.
      END IF


SWITCH51:
'SWITCH #51 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(51) = 1 THEN CLL51R = 1 ELSE CLL51R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL51R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #51
    TD(51) = 0                          ' make sure any time delay is reset
    IF SMFBN(51) <> 1 THEN GOTO L51END ' if switch is not normal (reversed)
    IF KEYSWITCH(51) = 1 THEN GOTO L51END 'if key still inserted skip processing
    UL(51) = 0                           '.... lock up the switch
    LED(51) = 0                           '... and set lock indication lights to off
    GOTO L51END

'** PROCESS UNLOCK PROTOCOL #51
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(51) = 1 THEN GOTO L51END        'if already unlocked branch to end
   IF BLK(30) = 1 THEN GOTO NOREL51      ' if switch interlock occupied go no release
   IF ((BLK(29) OR BLK(31)) = 1) THEN GOTO TIMEREL51    ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL51  ' if signal on either end cleared no release
  END IF

QUICKREL51:
'*** PERFORM QUICK RELEASE
   LED(51) = 0        ' set switch lock indicator lights to off
   TD(51) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(51) = 0 THEN GOTO L51END ' if key not inserted then skip
   UL(51) = 1         ' unlock switch and ...
   LED(51) = 1        ' turn on switch unlock indicator light
   GOTO L51END

TIMEREL51:
' *** PERFORM TIME RELEASE
   LED(51) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(51) = 0 THEN TD(51) = 30     ' if timer is not set, set it to desired level
   IF TD(51) > 0 THEN GOTO L51END    ' time delay is counting, skip to end
   IF TD(51) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(51) = 0 THEN GOTO L51END      ' key not inserted... skip
      TD(51) = 0                     ' ... reset timer =0 and ...
      UL(51) = 1                     ' unlock switch
      LED(51) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L51END                      ' branch to end of processing

NOREL51:
' *** PERFORM NO RELEASE
  TD(51) = 0                      ' make sure any time delay is reset
  UL(51) = 0                      ' .... and keep switch locked
  LED(51) = 0
' lock processing complete

L51END:

      IF UL(51) = 1 THEN
        IF SWITCHREV(51) = 1 THEN SM(51) = TUR:  'Unlocked and reversed.
        IF SWITCHREV(51) = 0 THEN SM(51) = TUN   'Unlocked and normal.
      END IF

SWITCH49:
'SWITCH #49 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(49) = 1 THEN CLL49R = 1 ELSE CLL49R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL49R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #49
    TD(49) = 0                          ' make sure any time delay is reset
    IF SMFBN(49) <> 1 THEN GOTO L49END ' if switch is not normal (reversed)
    IF KEYSWITCH(49) = 1 THEN GOTO L49END 'if key still inserted skip processing
    UL(49) = 0                           '.... lock up the switch
    LED(49) = 0                           '... and set lock indication lights to off
    GOTO L49END

'** PROCESS UNLOCK PROTOCOL #49
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(49) = 1 THEN GOTO L49END        'if already unlocked branch to end
   IF BLK(32) = 1 THEN GOTO NOREL49      ' if switch interlock occupied go no release
   IF ((BLK(29) OR BLK(31) OR BLK(33)) = 1) THEN GOTO TIMEREL49   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL49  ' if signal on either end cleared no release
  END IF

QUICKREL49:
'*** PERFORM QUICK RELEASE
   LED(49) = 0        ' set switch lock indicator lights to off
   TD(49) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(49) = 0 THEN GOTO L49END ' if key not inserted then skip
   UL(49) = 1         ' unlock switch and ...
   LED(49) = 1        ' turn on switch unlock indicator light
   GOTO L49END

TIMEREL49:
' *** PERFORM TIME RELEASE
   LED(49) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(49) = 0 THEN TD(49) = 30     ' if timer is not set, set it to desired level
   IF TD(49) > 0 THEN GOTO L49END    ' time delay is counting, skip to end
   IF TD(49) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(49) = 0 THEN GOTO L49END      ' key not inserted... skip
      TD(49) = 0                     ' ... reset timer =0 and ...
      UL(49) = 1                     ' unlock switch
      LED(49) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L49END                      ' branch to end of processing

NOREL49:
' *** PERFORM NO RELEASE
  TD(49) = 0                      ' make sure any time delay is reset
  UL(49) = 0                      ' .... and keep switch locked
  LED(49) = 0
' lock processing complete

L49END:

      IF UL(49) = 1 THEN
        IF SWITCHREV(49) = 1 THEN SM(49) = TUR:  'Unlocked and reversed.
        IF SWITCHREV(49) = 0 THEN SM(49) = TUN   'Unlocked and normal.
      END IF

SWITCH47:
'SWITCH #47 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(47) = 1 THEN CLL47R = 1 ELSE CLL47R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL47R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #47
    TD(47) = 0                          ' make sure any time delay is reset
    IF SMFBN(47) <> 1 THEN GOTO L47END ' if switch is not normal (reversed)
    IF KEYSWITCH(47) = 1 THEN GOTO L47END 'if key still inserted skip processing
    UL(47) = 0                           '.... lock up the switch
    LED(47) = 0                           '... and set lock indication lights to off
    GOTO L47END

'** PROCESS UNLOCK PROTOCOL #47
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(47) = 1 THEN GOTO L47END        'if already unlocked branch to end
   IF BLK(32) = 1 THEN GOTO NOREL47      ' if switch interlock occupied go no release
   IF ((BLK(28) OR BLK(29)) = 1) THEN GOTO TIMEREL47    ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL47  ' if signal on either end cleared no release
  END IF

QUICKREL47:
'*** PERFORM QUICK RELEASE
   LED(47) = 0        ' set switch lock indicator lights to off
   TD(47) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(47) = 0 THEN GOTO L47END ' if key not inserted then skip
   UL(47) = 1         ' unlock switch and ...
   LED(47) = 1        ' turn on switch unlock indicator light
   GOTO L47END

TIMEREL47:
' *** PERFORM TIME RELEASE
   LED(47) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(47) = 0 THEN TD(47) = 30     ' if timer is not set, set it to desired level
   IF TD(47) > 0 THEN GOTO L47END    ' time delay is counting, skip to end
   IF TD(47) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(47) = 0 THEN GOTO L47END      ' key not inserted... skip
      TD(47) = 0                     ' ... reset timer =0 and ...
      UL(47) = 1                     ' unlock switch
      LED(47) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L47END                      ' branch to end of processing

NOREL47:
' *** PERFORM NO RELEASE
  TD(47) = 0                      ' make sure any time delay is reset
  UL(47) = 0                      ' .... and keep switch locked
  LED(47) = 0
' lock processing complete

L47END:

      IF UL(47) = 1 THEN
        IF SWITCHREV(47) = 1 THEN SM(47) = TUR:  'Unlocked and reversed.
        IF SWITCHREV(47) = 0 THEN SM(47) = TUN   'Unlocked and normal.
      END IF



REM ********************* Sparta ***************************

SWITCH45:
'SWITCH #45 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(45) = 1 THEN CLL45R = 1 ELSE CLL45R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL45R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #45
    TD(45) = 0                          ' make sure any time delay is reset
    IF SMFBN(45) <> 1 THEN GOTO L45END ' if switch is not normal (reversed)
    IF KEYSWITCH(45) = 1 THEN GOTO L45END 'if key still inserted skip processing
    UL(45) = 0                           '.... lock up the switch
    LED(45) = 0                           '... and set lock indication lights to off
    GOTO L45END

'** PROCESS UNLOCK PROTOCOL #45
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(45) = 1 THEN GOTO L45END        'if already unlocked branch to end
   IF BLK(37) = 1 THEN GOTO NOREL45      ' if switch interlock occupied go no release
   IF (BLK(33) = 1 OR BLK(38) = 1 OR BLK(39) = 1) THEN GOTO TIMEREL45' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL45  ' if signal on either end cleared no release
  END IF

QUICKREL45:
'*** PERFORM QUICK RELEASE
   LED(45) = 0        ' set switch lock indicator lights to off
   TD(45) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(45) = 0 THEN GOTO L45END ' if key not inserted then skip
   UL(45) = 1         ' unlock switch and ...
   LED(45) = 1        ' turn on switch unlock indicator light
   GOTO L45END

TIMEREL45:
' *** PERFORM TIME RELEASE
   LED(45) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(45) = 0 THEN TD(45) = 30     ' if timer is not set, set it to desired level
   IF TD(45) > 0 THEN GOTO L45END    ' time delay is counting, skip to end
   IF TD(45) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(45) = 0 THEN GOTO L45END      ' key not inserted... skip
      TD(45) = 0                     ' ... reset timer =0 and ...
      UL(45) = 1                     ' unlock switch
      LED(45) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L45END                      ' branch to end of processing

NOREL45:
' *** PERFORM NO RELEASE
  TD(45) = 0                      ' make sure any time delay is reset
  UL(45) = 0                      ' .... and keep switch locked
  LED(45) = 0
' lock processing complete

L45END:

      IF UL(45) = 1 THEN
        IF SWITCHREV(45) = 1 THEN SM(45) = TUR
        IF SWITCHREV(45) = 0 THEN SM(45) = TUN
      END IF

SWITCH43: 'SWITCH #43 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(43) = 1 THEN CLL43R = 1 ELSE CLL43R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL43R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #43
    TD(43) = 0                          ' make sure any time delay is reset
    IF SMFBN(43) <> 1 THEN GOTO L43END ' if switch is not normal (reversed)
    IF KEYSWITCH(43) = 1 THEN GOTO L43END 'if key still inserted skip processing
    UL(43) = 0                           '.... lock up the switch
    LED(43) = 0                           '... and set lock indication lights to off
    GOTO L43END

'** PROCESS UNLOCK PROTOCOL #43
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(43) = 1 THEN GOTO L43END        'if already unlocked branch to end
   IF BLK(38) = 1 THEN GOTO NOREL43      ' if switch interlock occupied go no release
   IF (BLK(33) + BLK(37) + BLK(39) + BLK(41) + BLK(42) <> 0) THEN GOTO TIMEREL43' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL43  ' if signal on either end cleared no release
  END IF

QUICKREL43:
'*** PERFORM QUICK RELEASE
   LED(43) = 0        ' set switch lock indicator lights to off
   TD(43) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(43) = 0 THEN GOTO L43END ' if key not inserted then skip
   UL(43) = 1         ' unlock switch and ...
   LED(43) = 1        ' turn on switch unlock indicator light
   GOTO L43END

TIMEREL43:
' *** PERFORM TIME RELEASE
   LED(43) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(43) = 0 THEN TD(43) = 30     ' if timer is not set, set it to desired level
   IF TD(43) > 0 THEN GOTO L43END    ' time delay is counting, skip to end
   IF TD(43) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(43) = 0 THEN GOTO L43END      ' key not inserted... skip
      TD(43) = 0                     ' ... reset timer =0 and ...
      UL(43) = 1                     ' unlock switch
      LED(43) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L43END                      ' branch to end of processing

NOREL43:
' *** PERFORM NO RELEASE
  TD(43) = 0                      ' make sure any time delay is reset
  UL(43) = 0                      ' .... and keep switch locked
  LED(43) = 0
' lock processing complete

L43END:

      IF UL(43) = 1 THEN
        IF SWITCHREV(43) = 1 THEN SM(43) = TUR:  'Unlocked and reversed.
        IF SWITCHREV(43) = 0 THEN SM(43) = TUN   'Unlocked and normal.
      END IF

SWITCH41:
'SWITCH #41 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(41) = 1 THEN CLL41R = 1 ELSE CLL41R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL41R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #41
    TD(41) = 0                          ' make sure any time delay is reset
    IF SMFBN(41) <> 1 THEN GOTO L41END ' if switch is not normal (reversed)
    IF KEYSWITCH(41) = 1 THEN GOTO L41END 'if key still inserted skip processing
    UL(41) = 0                           '.... lock up the switch
    LED(41) = 0                           '... and set lock indication lights to off
    GOTO L41END

'** PROCESS UNLOCK PROTOCOL #41
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(41) = 1 THEN GOTO L41END        'if already unlocked branch to end
   IF BLK(42) = 1 THEN GOTO NOREL41      ' if switch interlock occupied go no release
   IF (BLK(45) OR BLK(44) OR BLK(43) OR BLK(39) = 1 OR BLK(38) = 1) THEN GOTO TIMEREL41  ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL41  ' if signal on either end cleared no release
  END IF

QUICKREL41:
'*** PERFORM QUICK RELEASE
   LED(41) = 0        ' set switch lock indicator lights to off
   TD(41) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(41) = 0 THEN GOTO L41END ' if key not inserted then skip
   UL(41) = 1         ' unlock switch and ...
   LED(41) = 1        ' turn on switch unlock indicator light
   GOTO L41END

TIMEREL41:
' *** PERFORM TIME RELEASE
   LED(41) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(41) = 0 THEN TD(41) = 30     ' if timer is not set, set it to desired level
   IF TD(41) > 0 THEN GOTO L41END    ' time delay is counting, skip to end
   IF TD(41) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(41) = 0 THEN GOTO L41END      ' key not inserted... skip
      TD(41) = 0                     ' ... reset timer =0 and ...
      UL(41) = 1                     ' unlock switch
      LED(41) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L41END                      ' branch to end of processing

NOREL41:
' *** PERFORM NO RELEASE
  TD(41) = 0                      ' make sure any time delay is reset
  UL(41) = 0                      ' .... and keep switch locked
  LED(41) = 0
' lock processing complete

L41END:

      IF UL(41) = 1 THEN
        IF SWITCHREV(41) = 1 THEN SM(41) = TUR
        IF SWITCHREV(41) = 0 THEN SM(41) = TUN
      END IF


SWITCH39:
'SWITCH #39 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(39) = 1 THEN CLL39R = 1 ELSE CLL39R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL39R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #39
    TD(39) = 0                          ' make sure any time delay is reset
    IF SMFBN(39) <> 1 THEN GOTO L39END ' if switch is not normal (reversed)
    IF KEYSWITCH(39) = 1 THEN GOTO L39END 'if key still inserted skip processing
    UL(39) = 0                           '.... lock up the switch
    LED(39) = 0                           '... and set lock indication lights to off
    GOTO L39END

'** PROCESS UNLOCK PROTOCOL #39
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(39) = 1 THEN GOTO L39END        'if already unlocked branch to end
   IF BLK(44) = 1 THEN GOTO NOREL39      ' if switch interlock occupied go no release
   IF ((BLK(45) OR BLK(43) OR BLK(42) OR BLK(39)) = 1) THEN GOTO TIMEREL39  ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL39  ' if signal on either end cleared no release
  END IF

QUICKREL39:
'*** PERFORM QUICK RELEASE
   LED(39) = 0        ' set switch lock indicator lights to off
   TD(39) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(39) = 0 THEN GOTO L39END ' if key not inserted then skip
   UL(39) = 1         ' unlock switch and ...
   LED(39) = 1        ' turn on switch unlock indicator light
   GOTO L39END

TIMEREL39:
' *** PERFORM TIME RELEASE
   LED(39) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(39) = 0 THEN TD(39) = 30     ' if timer is not set, set it to desired level
   IF TD(39) > 0 THEN GOTO L39END    ' time delay is counting, skip to end
   IF TD(39) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(39) = 0 THEN GOTO L39END      ' key not inserted... skip
      TD(39) = 0                     ' ... reset timer =0 and ...
      UL(39) = 1                     ' unlock switch
      LED(39) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L39END                      ' branch to end of processing

NOREL39:
' *** PERFORM NO RELEASE
  TD(39) = 0                      ' make sure any time delay is reset
  UL(39) = 0                      ' .... and keep switch locked
  LED(39) = 0
' lock processing complete

L39END:

      IF UL(39) = 1 THEN
        IF SWITCHREV(39) = 1 THEN SM(39) = TUR
        IF SWITCHREV(39) = 0 THEN SM(39) = TUN
      END IF



REM ******************* Worthville *******************************

SWITCH37:
'SWITCH #37 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(37) = 1 THEN CLL37R = 1 ELSE CLL37R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL37R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #37
    TD(37) = 0                          ' make sure any time delay is reset
    IF SMFBN(37) <> 1 THEN GOTO L37END ' if switch is not normal (reversed)
    IF KEYSWITCH(37) = 1 THEN GOTO L37END 'if key still inserted skip processing
    UL(37) = 0                           '.... lock up the switch
    LED(37) = 0                           '... and set lock indication lights to off
    GOTO L37END

'** PROCESS UNLOCK PROTOCOL #37
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(37) = 1 THEN GOTO L37END        'if already unlocked branch to end
   IF BLK(49) = 1 THEN GOTO NOREL37      ' if switch interlock occupied go no release
   IF ((BLK(45) OR BLK(50) OR BLK(51)) = 1) THEN GOTO TIMEREL37   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL37  ' if signal on either end cleared no release
  END IF

QUICKREL37:
'*** PERFORM QUICK RELEASE
   LED(37) = 0        ' set switch lock indicator lights to off
   TD(37) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(37) = 0 THEN GOTO L37END ' if key not inserted then skip
   UL(37) = 1         ' unlock switch and ...
   LED(37) = 1        ' turn on switch unlock indicator light
   GOTO L37END

TIMEREL37:
' *** PERFORM TIME RELEASE
   LED(37) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(37) = 0 THEN TD(37) = 30     ' if timer is not set, set it to desired level
   IF TD(37) > 0 THEN GOTO L37END    ' time delay is counting, skip to end
   IF TD(37) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(37) = 0 THEN GOTO L37END      ' key not inserted... skip
      TD(37) = 0                     ' ... reset timer =0 and ...
      UL(37) = 1                     ' unlock switch
      LED(37) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L37END                      ' branch to end of processing

NOREL37:
' *** PERFORM NO RELEASE
  TD(37) = 0                      ' make sure any time delay is reset
  UL(37) = 0                      ' .... and keep switch locked
  LED(37) = 0
' lock processing complete

L37END:

      IF UL(37) = 1 THEN
        IF SWITCHREV(37) = 1 THEN SM(37) = TUR
        IF SWITCHREV(37) = 0 THEN SM(37) = TUN
      END IF

SWITCH35:
'SWITCH #35 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(35) = 1 THEN CLL35R = 1 ELSE CLL35R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL35R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #35
    TD(35) = 0                          ' make sure any time delay is reset
    IF SMFBN(35) <> 1 THEN GOTO L35END ' if switch is not normal (reversed)
    IF KEYSWITCH(35) = 1 THEN GOTO L35END 'if key still inserted skip processing
    UL(35) = 0                           '.... lock up the switch
    LED(35) = 0                           '... and set lock indication lights to off
    GOTO L35END

'** PROCESS UNLOCK PROTOCOL #35
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(35) = 1 THEN GOTO L35END        'if already unlocked branch to end
   IF BLK(52) = 1 THEN GOTO NOREL35      ' if switch interlock occupied go no release
   IF ((BLK(50) OR BLK(60) OR BLK(56)) = 1) THEN GOTO TIMEREL35   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL35  ' if signal on either end cleared no release
  END IF

QUICKREL35:
'*** PERFORM QUICK RELEASE
   LED(35) = 0        ' set switch lock indicator lights to off
   TD(35) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(35) = 0 THEN GOTO L35END ' if key not inserted then skip
   UL(35) = 1         ' unlock switch and ...
   LED(35) = 1        ' turn on switch unlock indicator light
   GOTO L35END

TIMEREL35:
' *** PERFORM TIME RELEASE
   LED(35) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(35) = 0 THEN TD(35) = 20     ' if timer is not set, set it to desired level
   IF TD(35) > 0 THEN GOTO L35END    ' time delay is counting, skip to end
   IF TD(35) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(35) = 0 THEN GOTO L35END      ' key not inserted... skip
      TD(35) = 0                     ' ... reset timer =0 and ...
      UL(35) = 1                     ' unlock switch
      LED(35) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L35END                      ' branch to end of processing

NOREL35:
' *** PERFORM NO RELEASE
  TD(35) = 0                      ' make sure any time delay is reset
  UL(35) = 0                      ' .... and keep switch locked
  LED(35) = 0
' lock processing complete

L35END:

      IF UL(35) = 1 THEN
        IF SWITCHREV(35) = 1 THEN SM(35) = TUR: 'unlocked and reversed/open
        IF SWITCHREV(35) = 0 THEN SM(35) = TUN: ' unlocked and closed/normal
      END IF


SWITCH33:
'SWITCH #33 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(33) = 1 THEN CLL33R = 1 ELSE CLL33R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL33R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #33
    TD(33) = 0                          ' make sure any time delay is reset
    IF SMFBN(33) <> 1 THEN GOTO L33END ' if switch is not normal (reversed)
    IF KEYSWITCH(33) = 1 THEN GOTO L33END 'if key still inserted skip processing
    UL(33) = 0                           '.... lock up the switch
    LED(33) = 0                           '... and set lock indication lights to off
    GOTO L33END

'** PROCESS UNLOCK PROTOCOL #33
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(33) = 1 THEN GOTO L33END        'if already unlocked branch to end
   IF (BLK(53) OR BLK(58)) = 1 THEN GOTO NOREL33     ' if switch interlock occupied go no release
   IF ((BLK(51) OR BLK(54) OR BLK(55) OR BLK(60) = 1)) THEN GOTO TIMEREL33   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL33  ' if signal on either end cleared no release
  END IF

QUICKREL33:
'*** PERFORM QUICK RELEASE
   LED(33) = 0        ' set switch lock indicator lights to off
   TD(33) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(33) = 0 THEN GOTO L33END ' if key not inserted then skip
   UL(33) = 1         ' unlock switch and ...
   LED(33) = 1        ' turn on switch unlock indicator light
   GOTO L33END

TIMEREL33:
' *** PERFORM TIME RELEASE
   LED(33) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(33) = 0 THEN TD(33) = 20     ' if timer is not set, set it to desired level
   IF TD(33) > 0 THEN GOTO L33END    ' time delay is counting, skip to end
   IF TD(33) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(33) = 0 THEN GOTO L33END      ' key not inserted... skip
      TD(33) = 0                     ' ... reset timer =0 and ...
      UL(33) = 1                     ' unlock switch
      LED(33) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L33END                      ' branch to end of processing

NOREL33:
' *** PERFORM NO RELEASE
  TD(33) = 0                      ' make sure any time delay is reset
  UL(33) = 0                      ' .... and keep switch locked
  LED(33) = 0
' lock processing complete

L33END:

      IF UL(33) = 1 THEN
        IF SWITCHREV(33) = 1 THEN SM(33) = TUR: 'unlocked and open/reversed
        IF SWITCHREV(33) = 0 THEN SM(33) = TUN: 'unlocked and normal/closed
      END IF


SWITCH31:
'SWITCH #31 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(31) = 1 THEN CLL31R = 1 ELSE CLL31R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL31R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #31
    TD(31) = 0                          ' make sure any time delay is reset
    IF SMFBN(31) <> 1 THEN GOTO L31END ' if switch is not normal (reversed)
    IF KEYSWITCH(31) = 1 THEN GOTO L31END 'if key still inserted skip processing
    UL(31) = 0                           '.... lock up the switch
    LED(31) = 0                           '... and set lock indication lights to off
    GOTO L31END

'** PROCESS UNLOCK PROTOCOL #31
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(31) = 1 THEN GOTO L31END        'if already unlocked branch to end
   IF (BLK(57) OR BLK(59)) = 1 THEN GOTO NOREL31     ' if switch interlock occupied go no release
   IF ((BLK(55) OR BLK(56) OR BLK(62) OR BLK(63) OR BLK(64)) = 1) THEN GOTO TIMEREL31    ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL31  ' if signal on either end cleared no release
  END IF

QUICKREL31:
'*** PERFORM QUICK RELEASE
   LED(31) = 0        ' set switch lock indicator lights to off
   TD(31) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(31) = 0 THEN GOTO L31END ' if key not inserted then skip
   UL(31) = 1         ' unlock switch and ...
   LED(31) = 1        ' turn on switch unlock indicator light
   GOTO L31END

TIMEREL31:
' *** PERFORM TIME RELEASE
   LED(31) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(31) = 0 THEN TD(31) = 25     ' if timer is not set, set it to desired level
   IF TD(31) > 0 THEN GOTO L31END    ' time delay is counting, skip to end
   IF TD(31) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(31) = 0 THEN GOTO L31END      ' key not inserted... skip
      TD(31) = 0                     ' ... reset timer =0 and ...
      UL(31) = 1                     ' unlock switch
      LED(31) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L31END                      ' branch to end of processing

NOREL31:
' *** PERFORM NO RELEASE
  TD(31) = 0                      ' make sure any time delay is reset
  UL(31) = 0                      ' .... and keep switch locked
  LED(31) = 0
' lock processing complete

L31END:

      IF UL(31) = 1 THEN
        IF SWITCHREV(31) = 1 THEN SM(31) = TUR: ' unlocked open/reverse
        IF SWITCHREV(31) = 0 THEN SM(31) = TUN: ' unlocked closed/normal
      END IF


SWITCH29:
'SWITCH #29 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(29) = 1 THEN CLL29R = 1 ELSE CLL29R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL29R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #29
    TD(29) = 0                          ' make sure any time delay is reset
    IF SMFBN(29) <> 1 THEN GOTO L29END ' if switch is not normal (reversed)
    IF KEYSWITCH(29) = 1 THEN GOTO L29END 'if key still inserted skip processing
    UL(29) = 0                           '.... lock up the switch
    LED(29) = 0                           '... and set lock indication lights to off
    GOTO L29END

'** PROCESS UNLOCK PROTOCOL #29
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(29) = 1 THEN GOTO L29END        'if already unlocked branch to end
   IF BLK(62) = 1 THEN GOTO NOREL29      ' if switch interlock occupied go no release
   IF ((BLK(54) OR BLK(55) OR BLK(59) OR BLK(63)) = 1) THEN GOTO TIMEREL29   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL29  ' if signal on either end cleared no release
  END IF

QUICKREL29:
'*** PERFORM QUICK RELEASE
   LED(29) = 0        ' set switch lock indicator lights to off
   TD(29) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(29) = 0 THEN GOTO L29END ' if key not inserted then skip
   UL(29) = 1         ' unlock switch and ...
   LED(29) = 1        ' turn on switch unlock indicator light
   GOTO L29END

TIMEREL29:
' *** PERFORM TIME RELEASE
   LED(29) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(29) = 0 THEN TD(29) = 5    ' if timer is not set, set it to desired level
   IF TD(29) > 0 THEN GOTO L29END    ' time delay is counting, skip to end
   IF TD(29) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(29) = 0 THEN GOTO L29END      ' key not inserted... skip
      TD(29) = 0                     ' ... reset timer =0 and ...
      UL(29) = 1                     ' unlock switch
      LED(29) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L29END                      ' branch to end of processing

NOREL29:
' *** PERFORM NO RELEASE
  TD(29) = 0                      ' make sure any time delay is reset
  UL(29) = 0                      ' .... and keep switch locked
 LED(29) = 0
' lock processing complete

L29END:

      IF UL(29) = 1 THEN
        IF SWITCHREV(29) = 1 THEN SM(29) = TUR  'unlocked & open
        IF SWITCHREV(29) = 0 THEN SM(29) = TUN: 'unlocked & closed
      END IF

REM ********************* Campbellsburg ***************************

SWITCH27:
'SWITCH #27 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(27) = 1 THEN CLL27R = 1 ELSE CLL27R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL27R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #27
    TD(27) = 0                          ' make sure any time delay is reset
    IF SMFBN(27) <> 1 THEN GOTO L27END ' if switch is not normal (reversed)
    IF KEYSWITCH(27) = 1 THEN GOTO L27END 'if key still inserted skip processing
    UL(27) = 0                           '.... lock up the switch
    LED(27) = 0                           '... and set lock indication lights to off
    GOTO L27END

'** PROCESS UNLOCK PROTOCOL #27
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(27) = 1 THEN GOTO L27END        'if already unlocked branch to end
   IF BLK(74) = 1 THEN GOTO NOREL27      ' if switch interlock occupied go no release
   IF ((BLK(73) OR BLK(75) OR BLK(76)) = 1) THEN GOTO TIMEREL27   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL27 ' if signal on either end cleared no release
  END IF

QUICKREL27:
'*** PERFORM QUICK RELEASE
   LED(27) = 0        ' set switch lock indicator lights to off
   TD(27) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(27) = 0 THEN GOTO L27END ' if key not inserted then skip
   UL(27) = 1         ' unlock switch and ...
   LED(27) = 1        ' turn on switch unlock indicator light
   GOTO L27END

TIMEREL27:
' *** PERFORM TIME RELEASE
   LED(27) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(27) = 0 THEN TD(27) = 30     ' if timer is not set, set it to desired level
   IF TD(27) > 0 THEN GOTO L27END    ' time delay is counting, skip to end
   IF TD(27) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(27) = 0 THEN GOTO L27END      ' key not inserted... skip
      TD(27) = 0                     ' ... reset timer =0 and ...
      UL(27) = 1                     ' unlock switch
      LED(27) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L27END                      ' branch to end of processing

NOREL27:
' *** PERFORM NO RELEASE
  TD(27) = 0                      ' make sure any time delay is reset
  UL(27) = 0                      ' .... and keep switch locked
  LED(27) = 0
' lock processing complete

L27END:

      IF UL(27) = 1 THEN
        IF SWITCHREV(27) = 1 THEN SM(27) = TUR
        IF SWITCHREV(27) = 0 THEN SM(27) = TUN
      END IF

SWITCH25:
'SWITCH #25 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(25) = 1 THEN CLL25R = 1 ELSE CLL25R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL25R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #25
    TD(25) = 0                          ' make sure any time delay is reset
    IF SMFBN(25) <> 1 THEN GOTO L25END ' if switch is not normal (reversed)
    IF KEYSWITCH(25) = 1 THEN GOTO L25END 'if key still inserted skip processing
    UL(25) = 0                           '.... lock up the switch
    LED(25) = 0                           '... and set lock indication lights to off
    GOTO L25END

'** PROCESS UNLOCK PROTOCOL #25
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(25) = 1 THEN GOTO L25END        'if already unlocked branch to end
   IF BLK(77) = 1 THEN GOTO NOREL25      ' if switch interlock occupied go no release
   IF ((BLK(74) OR BLK(75) OR BLK(78)) = 1) THEN GOTO TIMEREL25   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL25 ' if signal on either end cleared no release
  END IF

QUICKREL25:
'*** PERFORM QUICK RELEASE
   LED(25) = 0        ' set switch lock indicator lights to off
   TD(25) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(25) = 0 THEN GOTO L25END ' if key not inserted then skip
   UL(25) = 1         ' unlock switch and ...
   LED(25) = 1        ' turn on switch unlock indicator light
   GOTO L25END

TIMEREL25:
' *** PERFORM TIME RELEASE
   LED(25) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(25) = 0 THEN TD(25) = 30     ' if timer is not set, set it to desired level
   IF TD(25) > 0 THEN GOTO L25END    ' time delay is counting, skip to end
   IF TD(25) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(25) = 0 THEN GOTO L25END      ' key not inserted... skip
      TD(25) = 0                     ' ... reset timer =0 and ...
      UL(25) = 1                     ' unlock switch
      LED(25) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L25END                      ' branch to end of processing

NOREL25:
' *** PERFORM NO RELEASE
  TD(25) = 0                      ' make sure any time delay is reset
  UL(25) = 0                      ' .... and keep switch locked
  LED(25) = 0
' lock processing complete

L25END:

      IF UL(25) = 1 THEN
        IF SWITCHREV(25) = 1 THEN SM(25) = TUR
        IF SWITCHREV(25) = 0 THEN SM(25) = TUN
      END IF

SWITCH23:
'SWITCH #23 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(23) = 1 THEN CLL23R = 1 ELSE CLL23R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL23R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #23
    TD(23) = 0                          ' make sure any time delay is reset
    IF SMFBN(23) <> 1 THEN GOTO L23END ' if switch is not normal (reversed)
    IF KEYSWITCH(23) = 1 THEN GOTO L23END 'if key still inserted skip processing
    UL(23) = 0                           '.... lock up the switch
    LED(23) = 0                           '... and set lock indication lights to off
    GOTO L23END

'** PROCESS UNLOCK PROTOCOL #23
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(23) = 1 THEN GOTO L23END        'if already unlocked branch to end
   IF BLK(78) = 1 THEN GOTO NOREL23      ' if switch interlock occupied go no release
   IF ((BLK(75) OR BLK(79) OR BLK(81) OR BLK(82)) = 1) THEN GOTO TIMEREL23   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL23 ' if signal on either end cleared no release
  END IF

QUICKREL23:
'*** PERFORM QUICK RELEASE
   LED(23) = 0        ' set switch lock indicator lights to off
   TD(23) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(23) = 0 THEN GOTO L23END ' if key not inserted then skip
   UL(23) = 1         ' unlock switch and ...
   LED(23) = 1        ' turn on switch unlock indicator light
   GOTO L23END

TIMEREL23:
' *** PERFORM TIME RELEASE
   LED(23) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(23) = 0 THEN TD(23) = 30     ' if timer is not set, set it to desired level
   IF TD(23) > 0 THEN GOTO L23END    ' time delay is counting, skip to end
   IF TD(23) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(23) = 0 THEN GOTO L23END      ' key not inserted... skip
      TD(23) = 0                     ' ... reset timer =0 and ...
      UL(23) = 1                     ' unlock switch
      LED(23) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L23END                      ' branch to end of processing

NOREL23:
' *** PERFORM NO RELEASE
  TD(23) = 0                      ' make sure any time delay is reset
  UL(23) = 0                      ' .... and keep switch locked
  LED(23) = 0
' lock processing complete

L23END:

      IF UL(23) = 1 THEN
        IF SWITCHREV(23) = 1 THEN SM(23) = TUR
        IF SWITCHREV(23) = 0 THEN SM(23) = TUN
      END IF


SWITCH21:
'SWITCH #21 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(21) = 1 THEN CLL21R = 1 ELSE CLL21R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL21R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #21
    TD(21) = 0                          ' make sure any time delay is reset
    IF SMFBN(21) <> 1 THEN GOTO L21END ' if switch is not normal (reversed)
    IF KEYSWITCH(21) = 1 THEN GOTO L21END 'if key still inserted skip processing
    UL(21) = 0                           '.... lock up the switch
    LED(21) = 0                           '... and set lock indication lights to off
    GOTO L21END

'** PROCESS UNLOCK PROTOCOL #21
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(21) = 1 THEN GOTO L21END        'if already unlocked branch to end
   IF BLK(78) + BLK(80) = 1 THEN GOTO NOREL21     ' if switch interlock occupied go no release
   IF ((BLK(78) OR BLK(75) OR BLK(81)) = 1) THEN GOTO TIMEREL21   ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL21 ' if signal on either end cleared no release
  END IF

QUICKREL21:
'*** PERFORM QUICK RELEASE
   LED(21) = 0        ' set switch lock indicator lights to off
   TD(21) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(21) = 0 THEN GOTO L21END ' if key not inserted then skip
   UL(21) = 1         ' unlock switch and ...
   LED(21) = 1        ' turn on switch unlock indicator light
   GOTO L21END

TIMEREL21:
' *** PERFORM TIME RELEASE
   LED(21) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(21) = 0 THEN TD(21) = 30     ' if timer is not set, set it to desired level
   IF TD(21) > 0 THEN GOTO L21END    ' time delay is counting, skip to end
   IF TD(21) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(21) = 0 THEN GOTO L21END      ' key not inserted... skip
      TD(21) = 0                     ' ... reset timer =0 and ...
      UL(21) = 1                     ' unlock switch
      LED(21) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L21END                      ' branch to end of processing

NOREL21:
' *** PERFORM NO RELEASE
  TD(21) = 0                      ' make sure any time delay is reset
  UL(21) = 0                      ' .... and keep switch locked
  LED(21) = 0
' lock processing complete

L21END:

      IF UL(21) = 1 THEN
        IF SWITCHREV(21) = 1 THEN SM(21) = TUR
        IF SWITCHREV(21) = 0 THEN SM(21) = TUN
      END IF

SWITCH19:
'SWITCH #19 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(19) = 1 THEN CLL19R = 1 ELSE CLL19R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL19R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #19
    TD(19) = 0                          ' make sure any time delay is reset
    IF SMFBN(19) <> 1 THEN GOTO L19END ' if switch is not normal (reversed)
    IF KEYSWITCH(19) = 1 THEN GOTO L19END 'if key still inserted skip processing
    UL(19) = 0                           '.... lock up the switch
    LED(19) = 0                           '... and set lock indication lights to off
    GOTO L19END

'** PROCESS UNLOCK PROTOCOL #19
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(19) = 1 THEN GOTO L19END        'if already unlocked branch to end
   IF BLK(79) = 1 THEN GOTO NOREL19      ' if switch interlock occupied go no release
   IF ((BLK(76) OR BLK(75) OR BLK(78) OR BLK(82)) = 1) THEN GOTO TIMEREL19     ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL19 ' if signal on either end cleared no release
  END IF

QUICKREL19:
'*** PERFORM QUICK RELEASE
   LED(19) = 0        ' set switch lock indicator lights to off
   TD(19) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(19) = 0 THEN GOTO L19END ' if key not inserted then skip
   UL(19) = 1         ' unlock switch and ...
   LED(19) = 1        ' turn on switch unlock indicator light
   GOTO L19END

TIMEREL19:
' *** PERFORM TIME RELEASE
   LED(19) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(19) = 0 THEN TD(19) = 30     ' if timer is not set, set it to desired level
   IF TD(19) > 0 THEN GOTO L19END    ' time delay is counting, skip to end
   IF TD(19) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(19) = 0 THEN GOTO L19END      ' key not inserted... skip
      TD(19) = 0                     ' ... reset timer =0 and ...
      UL(19) = 1                     ' unlock switch
      LED(19) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L19END                      ' branch to end of processing

NOREL19:
' *** PERFORM NO RELEASE
  TD(19) = 0                      ' make sure any time delay is reset
  UL(19) = 0                      ' .... and keep switch locked
  LED(19) = 0
' lock processing complete

L19END:

      IF UL(19) = 1 THEN
        IF SWITCHREV(19) = 1 THEN SM(19) = TUR
        IF SWITCHREV(19) = 0 THEN SM(19) = TUN
      END IF


SWITCH17:
'SWITCH #17 CONTROLLED ELECTRIC SWITCH LOCK
' check if dispatcher lock lever request is normal or reverse
  IF KEYSWITCH(17) = 1 THEN CLL17R = 1 ELSE CLL17R = 0  ' temp statement to release lock untill CTC is installed
  IF CLL17R = 0 THEN     'If lock lever is normal=0 then process lock protocol...
                         ' ... else process unlock protocol.

'** PROCESS LOCK PROTOCOL #17
    TD(17) = 0                          ' make sure any time delay is reset
    IF SMFBN(17) <> 1 THEN GOTO L17END ' if switch is not normal (reversed)
    IF KEYSWITCH(17) = 1 THEN GOTO L17END 'if key still inserted skip processing
    UL(17) = 0                           '.... lock up the switch
    LED(17) = 0                           '... and set lock indication lights to off
    GOTO L17END

'** PROCESS UNLOCK PROTOCOL #17
  ELSE  '*** DISPATCHER UNLOCK REQUEST ACTIVE, PROCESS UNLOCK PROTOCOL
   IF UL(17) = 1 THEN GOTO L17END        'if already unlocked branch to end
   IF BLK(83) = 1 THEN GOTO NOREL17      ' if switch interlock occupied go no release
   IF BLK(81) + BLK(82) + BLK(84) >= 1 THEN GOTO TIMEREL17  ' if block containing switch is occupied goto time release
   'IF (TLV?? = RIGHT OR TLV?? = LEFT) THEN GOTO NOREL17  ' if signal on either end cleared no release
  END IF

QUICKREL17:
'*** PERFORM QUICK RELEASE
   LED(17) = 0        ' set switch lock indicator lights to off
   TD(17) = 0         ' make sure any time delay is reset to 0
   IF KEYSWITCH(17) = 0 THEN GOTO L17END ' if key not inserted then skip
   UL(17) = 1         ' unlock switch and ...
   LED(17) = 1        ' turn on switch unlock indicator light
   GOTO L17END

TIMEREL17:
' *** PERFORM TIME RELEASE
   LED(17) = FGRN     ' set switch lock indicator lights to flashing
   IF TD(17) = 0 THEN
     TD(17) = 30     ' if timer is not set, set it to desired level
     IF BLK(81) + BLK(82) + BLK(84) = 1 THEN TD(17) = TD(17) - 25: ' if no opposing traffic shorten delay
   END IF
   IF TD(17) > 0 THEN GOTO L17END    ' time delay is counting, skip to end
   IF TD(17) < 0 THEN                ' time has expired then .....
     IF KEYSWITCH(17) = 0 THEN GOTO L17END      ' key not inserted... skip
      TD(17) = 0                     ' ... reset timer =0 and ...
      UL(17) = 1                     ' unlock switch
      LED(17) = 1                    ' turn on switch lock indicator light
    END IF
    GOTO L17END                      ' branch to end of processing

NOREL17:
' *** PERFORM NO RELEASE
  TD(17) = 0                      ' make sure any time delay is reset
  UL(17) = 0                      ' .... and keep switch locked
  LED(17) = 0
' lock processing complete

L17END:
      IF UL(17) = 1 THEN
        IF SWITCHREV(17) = 1 THEN SM(17) = TUR
        IF SWITCHREV(17) = 0 THEN SM(17) = TUN
      END IF

IF Diagnose$ <> "T" GOTO 700

' lines below used in testing switch locks  SKIPPED IF DISPLAYING TOWN STATUS ON SCREEN
  
  SW = 29: ' switch number as on CTC panel by 2
  FOR L = 1 TO 6
  LOCATE L + 4, 1: PRINT "SW "; : PRINT SW; : PRINT "/"; : PRINT " SW-"; : IF SMFBN(SW) = 1 THEN PRINT "N" ELSE PRINT "R"
  LOCATE L + 4, 15: PRINT "/KEY "; : IF KEYSWITCH(SW) = 1 THEN PRINT "UNLOCK ";  ELSE PRINT "  LOCK "
  IF SMFBN(SW) <> 1 THEN COLOR 4
  LOCATE L + 4, 27: PRINT "/TOGGLE "; : IF SWITCHREV(SW) = 1 THEN PRINT "R";  ELSE PRINT "N";
  COLOR 7
  LOCATE L + 4, 37: IF UL(SW) = 1 THEN PRINT "UNLOCKED ";  ELSE PRINT "  LOCKED ";
  LOCATE L + 4, 46: PRINT "TIME DELAY"; : PRINT TD(SW); : PRINT " LIGHT "; : IF LED(SW) = 1 THEN PRINT " ON";  ELSE PRINT "OFF";
  'LOCATE L + 5, 1: PRINT "DISPATCHER CLL "; : PRINT CLL41R; :
  SW = SW + 2
  NEXT L


  LOCATE 11, 1:
  BL1 = 52: ' START AT BLOCK ...
  FOR M = BL1 TO (BL1 + 11)
    IF BLK(M) = 1 THEN CLOR(M) = 4 ELSE CLOR(M) = 7
    COLOR CLOR(M): PRINT "BLK("; : PRINT M; : PRINT ") "; : PRINT BLK(M);
  NEXT M
  LOCATE 13, 1
'  BL1 = 168
'  FOR M = BL1 TO (BL1 + 2)
'    IF BLK(M) = 1 THEN CLOR(M) = 4 ELSE CLOR(M) = 7
'    COLOR CLOR(M): PRINT "BLK("; : PRINT M; : PRINT ") "; : PRINT BLK(M);
'  NEXT M
'  COLOR 7
'  PRINT "BLK 20-19 "; : PRINT BLK(20) + BLK(21) + BLK(168) + BLK(19)

  PRINT ""
  LOCATE 15, 1
  SIG = 30
  FOR I = SIG TO SIG + 4 STEP 2
   IF SIGR(I) = 164 THEN SIGL$(I) = "R/R/R"
   IF SIGR(I) = 100 THEN SIGL$(I) = "R/R/Y"
   IF SIGR(I) = 148 THEN SIGL$(I) = "R/Y/R"
   IF SIGR(I) = 140 THEN SIGL$(I) = "R/G/R"
   IF SIGR(I) = 162 THEN SIGL$(I) = "Y/R/R"
   IF SIGR(I) = 161 THEN SIGL$(I) = "G/R/R"
   IF SIGL(I) = 164 THEN SIGL$(I) = "R/R/R"
   IF SIGL(I) = 100 THEN SIGL$(I) = "R/R/Y"
   IF SIGL(I) = 148 THEN SIGL$(I) = "R/Y/R"
   IF SIGL(I) = 140 THEN SIGL$(I) = "R/G/R"
   IF SIGL(I) = 162 THEN SIGL$(I) = "Y/R/R"
   IF SIGL(I) = 161 THEN SIGL$(I) = "G/R/R"
   IF SIGR(I) = 36 THEN SIGR$(I) = "R/R"
   IF SIGR(I) = 34 THEN SIGR$(I) = "R/Y"
   IF SIGR(I) = 20 THEN SIGR$(I) = "Y/R"
   IF SIGR(I) = 33 THEN SIGR$(I) = "R/G"
   IF SIGR(I) = 12 THEN SIGR$(I) = "G/R"
   IF SIGR(I) = 4 THEN SIGR$(I) = "R"
   IF SIGR(I) = 2 THEN SIGR$(I) = "Y"
   IF SIGR(I) = 1 THEN SIGR$(I) = "G"
   IF SIGL(I) = 36 THEN SIGL$(I) = "R/R"
   IF SIGL(I) = 34 THEN SIGL$(I) = "R/Y"
   IF SIGL(I) = 20 THEN SIGL$(I) = "Y/R"
   IF SIGL(I) = 33 THEN SIGL$(I) = "R/G"
   IF SIGL(I) = 12 THEN SIGL$(I) = "G/R"
   IF SIGL(I) = 4 THEN SIGL$(I) = "R"
   IF SIGL(I) = 2 THEN SIGL$(I) = "Y"
   IF SIGL(I) = 1 THEN SIGL$(I) = "G"

   PRINT "SIGL"; : PRINT I; : PRINT " "; : PRINT SIGL(I); : PRINT SIGL$(I)
   PRINT "SIGR"; : PRINT I; : PRINT " "; : PRINT SIGR(I); : PRINT SIGR$(I)
  NEXT I

' LOCATE 10, 60: PRINT "T1SAVE& "; : PRINT T1SAVE&


700

END SUB

SUB TESTOUTPUTS

REM PACK SUSIC1 DeCoursey Yard Control Panel Lights
                ' CARD 3, 4 outputs bi color LED for panel
               OB(5) = 85
               OB(6) = 85
               OB(7) = 85
               OB(8) = 85

               ' CARD 5, 1 output red LED for panel
               OB(9) = 63

                ' CARD 7, 4 outputs TEMPORARY TEST
               'OB(13) = 85
               'OB(14) = 85
               'OB(15) = 85
               'OB(16) = 85


            LOCATE 22, 1: PRINT "SUSIC#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
            PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6); : PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8);
            PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10); : PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12)

            UA = 16: NO = 40
            CALL OUTPUTS


CALL HEADER
LOCATE 11, 25: PRINT "DeCoursey Control Panel Lights On!"
LOCATE 13, 25: PRINT "Press any key to continue test.";
210 Inpt$ = INKEY$
IF Inpt$ = "" GOTO 210
LOCATE 13, 25: PRINT "                               "

DIM PND$(12)
 PND$(1) = "A": PND$(2) = "B": PND$(3) = "C": PND$(4) = "D"
 PND$(5) = "E": PND$(6) = "F": PND$(7) = "G": PND$(8) = "H"
 PND$(9) = "I": PND$(10) = "J": PND$(11) = "K": PND$(12) = "L"

 Delay! = .2

REM *******BEGIN TEST LOOP*******
FOR J = 1 TO 5
       LOCATE 13, 52: : PRINT "Pass # "; : PRINT J
       LOCATE 13, 63: PRINT "Delay "; : PRINT USING "#.##"; Delay!
     REM**INITIALIZE LEDS TO OFF
       FOR I = 5 TO 12
        OB(I) = 0
       NEXT I
     REM**OUTPUT PORT TO BE TESTED IN A LOOP**
       FOR PN = 5 TO 9

     REM**INCREMENT DISPLAYED BIT NUMBER IN A LOOP
       FOR N = 0 TO 7 ' or should this be 4 for 5 lights on eact CTC position?

     REM**OUTPUT TEST STATUS TO MONITOR
       LOCATE 13, 25: PRINT "PORT = "; PND$(PN); " BIT NUMBER = "; N

     REM**SET UP TEST LED PATTERN
       OB(PN) = 2 ^ N    'Number 2 raised to power N
            LOCATE 22, 1: PRINT "SUSIC#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
            PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6); : PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8);
            PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10); : PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12)
     REM**OUTPUT LED DISPLAY DATA TO OUTPUT CARD VIA SUSIC
       CALL OUTPUTS

     REM**DELAY LOOP SO CAN OBSERVE LED STATUS
       GOSUB 290

     REM**COMPLETE BIT POSITION LOOP
       NEXT N

     REM**TURN OFF CURRENT PORT BEFORE INCREMENT TO THE NEXT PORT
       OB(PN) = 0
     REM**INCREMENT TO NEXT PORT
       NEXT PN

     REM reduce time delay
       Delay! = Delay! - .05
  NEXT J


    REM TURN ON ALL CTS BOARD LEDS GREEN
        OB(5) = 170: OB(6) = 170: OB(7) = 170: OB(8) = 170: OB(9) = 31
            LOCATE 22, 1: PRINT "SUSIC#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
            PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6); : PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8);
            PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10); : PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12)

        CALL OUTPUTS: Delay! = 2!: GOSUB 290

    REM TURN ON ALL CTS BOARD LEDS RED
        OB(5) = 85: OB(6) = 85: OB(7) = 85: OB(8) = 85: OB(9) = 31
            LOCATE 22, 1: PRINT "SUSIC#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
            PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6); : PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8);
            PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10); : PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12)

        CALL OUTPUTS: Delay! = 2!: GOSUB 290

   REM TURN OFF ALL CTS BOARD LEDS
       OB(5) = 0: OB(6) = 0: OB(7) = 0: OB(8) = 0:  OB(9) = 32: OB(10) = 0: OB(11) = 0: OB(12) = 0
            LOCATE 22, 1: PRINT "SUSIC#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
            PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6); : PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8);
            PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10); : PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12)
       CALL OUTPUTS: Delay! = .5: GOSUB 290

               LOCATE 11, 25: PRINT "Decoursey LIGHT TEST COMPLETE!     "
               LOCATE 13, 25: PRINT "Light test Walton                           "
        LOCATE 15, 25: PRINT "Press any key to continue test.";
215     Inpt$ = INKEY$
        IF Inpt$ = "" GOTO 215
        LOCATE 15, 25: PRINT "                               "

            UA = 1: NO = 48
            CALL OUTPUTS

 PND$(1) = "A": PND$(2) = "B": PND$(3) = "C"
 PND$(4) = "D": PND$(5) = "E": PND$(6) = "F"
 Delay! = .2

REM *******BEGIN TEST LOOP*******SMINI #1
FOR J = 1 TO 5
       LOCATE 15, 52: : PRINT "Pass # "; : PRINT J
       LOCATE 15, 63: PRINT "Delay "; : PRINT USING "#.##"; Delay!
     REM**INITIALIZE LEDS TO OFF
       FOR I = 1 TO 6
        OB(I) = 0
       NEXT I
     REM**OUTPUT PORT TO BE TESTED IN A LOOP**
       FOR PN = 1 TO 6

     REM**INCREMENT DISPLAYED BIT NUMBER IN A LOOP
       FOR N = 0 TO 7 ' or should this be 4 for 5 lights on each CTC position?

     REM**OUTPUT TEST STATUS TO MONITOR
       LOCATE 15, 25: PRINT "PORT = "; PND$(PN); " BIT NUMBER = "; N

     REM**SET UP TEST LED PATTERN
       OB(PN) = 2 ^ N    'Number 2 raised to power N
            LOCATE 22, 1: PRINT "SMINI#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
            PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
            
     REM**OUTPUT LED DISPLAY DATA TO OUTPUT CARD VIA SUSIC
       CALL OUTPUTS

     REM**DELAY LOOP SO CAN OBSERVE LED STATUS
       GOSUB 290

     REM**COMPLETE BIT POSITION LOOP
       NEXT N

     REM**TURN OFF CURRENT PORT BEFORE INCREMENT TO THE NEXT PORT
       OB(PN) = 0
     REM**INCREMENT TO NEXT PORT
       NEXT PN

     REM reduce time delay
       Delay! = Delay! - .05
  NEXT J


    REM TURN ON ALL CTS BOARD LEDS
        OB(1) = 255: OB(2) = 255: OB(3) = 255: OB(4) = 255: OB(5) = 255: OB(6) = 255
            LOCATE 22, 1: PRINT "SMINI#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
            PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6)

        CALL OUTPUTS: Delay! = 2!: GOSUB 290

   REM TURN OFF ALL CTS BOARD LEDS
       OB(5) = 0: OB(6) = 0: OB(7) = 0: OB(8) = 0:  OB(9) = 0: OB(10) = 0: OB(11) = 0: OB(12) = 0
            LOCATE 22, 1: PRINT "SUSIC#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
            PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6); : PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8);
            PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10); : PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12)
       CALL OUTPUTS: Delay! = .5: GOSUB 290

               LOCATE 11, 25: PRINT "SMINI #1 LIGHT TEST COMPLETE!           "
               LOCATE 13, 25: PRINT "Light test Sparta                           "
        LOCATE 15, 25: PRINT "Press any key to continue test.";
220     Inpt$ = INKEY$
        IF Inpt$ = "" GOTO 220
        LOCATE 15, 25: PRINT "                               "

            UA = 2: NO = 48
            CALL OUTPUTS

 PND$(1) = "A": PND$(2) = "B": PND$(3) = "C"
 PND$(4) = "D": PND$(5) = "E": PND$(6) = "F"
 Delay! = .2



REM *******BEGIN TEST LOOP*******SMINI #2
FOR J = 1 TO 5
       LOCATE 15, 52: : PRINT "Pass # "; : PRINT J
       LOCATE 15, 63: PRINT "Delay "; : PRINT USING "#.##"; Delay!
     REM**INITIALIZE LEDS TO OFF
       FOR I = 1 TO 6
        OB(I) = 0
       NEXT I
     REM**OUTPUT PORT TO BE TESTED IN A LOOP**
       FOR PN = 1 TO 6

     REM**INCREMENT DISPLAYED BIT NUMBER IN A LOOP
       FOR N = 0 TO 7 ' or should this be 4 for 5 lights on each CTC position?

     REM**OUTPUT TEST STATUS TO MONITOR
       LOCATE 15, 25: PRINT "PORT = "; PND$(PN); " BIT NUMBER = "; N

     REM**SET UP TEST LED PATTERN
       OB(PN) = 2 ^ N    'Number 2 raised to power N
            LOCATE 22, 1: PRINT "SMINI#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
            PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);

     REM**OUTPUT LED DISPLAY DATA TO OUTPUT CARD VIA SUSIC
       CALL OUTPUTS

     REM**DELAY LOOP SO CAN OBSERVE LED STATUS
       GOSUB 290

     REM**COMPLETE BIT POSITION LOOP
       NEXT N

     REM**TURN OFF CURRENT PORT BEFORE INCREMENT TO THE NEXT PORT
       OB(PN) = 0
     REM**INCREMENT TO NEXT PORT
       NEXT PN

     REM reduce time delay
       Delay! = Delay! - .05
  NEXT J


    REM TURN ON ALL CTS BOARD LEDS
        OB(1) = 255: OB(2) = 255: OB(3) = 255: OB(4) = 255: OB(5) = 255: OB(6) = 255
            LOCATE 22, 1: PRINT "SMINI#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
            PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6)

        CALL OUTPUTS: Delay! = 2!: GOSUB 290

   REM TURN OFF ALL CTS BOARD LEDS
       OB(5) = 0: OB(6) = 0: OB(7) = 0: OB(8) = 0:  OB(9) = 0: OB(10) = 0: OB(11) = 0: OB(12) = 0
            LOCATE 22, 1: PRINT "SUSIC#1 OUTPUT BYTES =";
            PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
            PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6); : PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8);
            PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10); : PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12)
       CALL OUTPUTS: Delay! = .5: GOSUB 290

               LOCATE 11, 25: PRINT "SMINI #2 LIGHT TEST COMPLETE!           "


283 REM INITALIZE CTC BOARD BY FOOLING IT TO THINK ALL PUSH BUTTONS = PRESSED
REM WILL SEARCH FOR RR STATUS TO DISPLAY CTC LIGHTS PROPERLY
'CALL READRR' GET INITIAL PARAMETERS FROM RR
'FOR I = 16 TO 30
' CTCPB(I) = PBP ' SET EACH PUSH BUTTON ON CTC PANEL = PUSHED
'NEXT I
GOTO 400

290   REM **Real Time Delay loop variable DELAY! is the min time delay
       Start! = TIMER
300    Finish! = TIMER
       IF Finish! - Start! < Delay! GOTO 300
      RETURN
400

REM this is to test wiring and operation of SM 1-20, 26-33, 38-44!

LOCATE 13, 25: PRINT "Test Switch Motors? (Y/N)?                      ";
600 Inpt$ = INKEY$
IF Inpt$ = "" GOTO 600
        IF UCASE$(Inpt$) <> "Y" THEN GOTO 650

LOCATE 13, 25: PRINT "Set Switch Motors? (N/R)?           ";
610 Inpt$ = INKEY$
IF Inpt$ = "" GOTO 610
        IF UCASE$(Inpt$) = "N" THEN
           SMstate = TUN
           Inpt$ = "Normal"
        ELSE
           SMstate = TUR
           Inpt$ = "Reverse"
        END IF

        LOCATE 13, 25: PRINT "Setting         Switch # ";
        LOCATE 13, 33: PRINT Inpt$

        FOR I = 1 TO 20
                SM(I) = SMstate
                Delay! = 2
                GOSUB 290
                CALL WRITERR
                LOCATE 13, 48: PRINT I
        NEXT I
   
        FOR I = 26 TO 33
                SM(I) = SMstate
                Delay! = 2
                GOSUB 290
                CALL WRITERR
                LOCATE 13, 48: PRINT I
        NEXT I

        FOR I = 38 TO 44
                SM(I) = SMstate
                Delay! = 2
                GOSUB 290
                CALL WRITERR
                LOCATE 13, 48: PRINT I
        NEXT I

        LOCATE 11, 25: PRINT "All Switch motors are set "; : PRINT Inpt$
        GOTO 400

650
END SUB

SUB TestSignals

TESTLOOP = 1
TD(1) = 3

' *************** Call Header the test signals in a loop until there is a key press
CALL HEADER

TESTLOUP:
SELECT CASE TESTLOOP
        CASE 1
         ASPECT$ = "DARK  "
         ASPECT = DARK
         ASPECTB = DARK
         ASPECTD = DARK
         ASPECTDB = DARK
         ASPECTTB = DARK
        CASE 2
         ASPECT$ = "RED   "
         ASPECT = RED
         ASPECTD = REDRED
         ASPECTB = REDB
         ASPECTDB = REDREDB
         ASPECTTB = REDREDREDB
        CASE 3
         ASPECT$ = "YELLOW"
         ASPECT = YEL
         ASPECTD = 15
         ASPECTB = YELB
         ASPECTDB = 18
         ASPECTTB = 82
        CASE 4
         ASPECT$ = "GREEN "
         ASPECT = GRN
         ASPECTD = 5
         ASPECTB = GRNB
         ASPECTDB = 9
         ASPECTTB = 9 + 64
         
END SELECT

LOCATE 5, 1: PRINT "All Signals "; : PRINT ASPECT$
        'WORTHVILLE
        SIGR(10) = ASPECTB: 'THIS SIGNAL TO BECOME SIGR(30) WHEN OTHERS RENUMBERED
        SIGL(29) = ASPECTB
        SIGR(30) = ASPECTDB: SIGL(30) = ASPECTDB
        SIGL(31) = ASPECTDB
        SIGL(32) = ASPECTD: SIGL(34) = ASPECTD
        SIGR(34) = ASPECTB: SIGR(32) = ASPECTDB
        SIGR(36) = ASPECTB: SIGR(37) = ASPECTB
        SIGL(36) = ASPECTDB
        SIGR(38) = ASPECTB: SIGR(39) = ASPECTB
        SIGL(38) = ASPECTDB
        'SPARTA
        SIGL(46) = ASPECTTB
        SIGR(46) = ASPECTB: SIGR(42) = ASPECTB: SIGR(44) = ASPECTB
        SIGL(42) = ASPECTB
        SIGL(40) = ASPECTB: SIGL(41) = ASPECTB
        SIGR(40) = ASPECTTB
        'WALTON
        SIGR(48) = ASPECTDB
        SIGL(48) = ASPECTB: SIGL(49) = ASPECTB
        SIGR(54) = ASPECTB: SIGR(55) = ASPECTB
        SIGL(54) = ASPECTDB
        'LATONIA
        SIGL(55) = ASPECTB: SIGL(56) = ASPECTB: SIGL(57) = ASPECTB
        SIGR(56) = ASPECTTB
        SIGR(58) = ASPECTB: SIGL(58) = ASPECTDB
        SIGR(60) = ASPECTDB: SIGL(60) = ASPECTB
        SIGR(61) = ASPECTB
        SIGL(62) = ASPECTDB: SIGR(62) = ASPECTB: SIGR(63) = ASPECTB

CALL TIMERCNT
IF TD(1) > 0 THEN GOTO 1999
CALL WRITERR
TD(1) = 3
TESTLOOP = TESTLOOP + 1
IF TESTLOOP = 5 THEN TESTLOOP = 1

LOCATE 16, 30: PRINT "Press any key to stop"
1999 Inpt$ = INKEY$
IF Inpt$ <> "" THEN GOTO 2000
GOTO TESTLOUP

2000
END SUB

SUB TIMERCNT
'************************** SUB TIMERCNT ******************************
'*** UTILITY SUBROUTINE TO EXECUTE MULTIPLE ASYCHRONOUS TIME DELAYS ***
'*** BY AUTOMATICALLY DEINCREMENTING EACH ACTIVE TIME DELAY BY 1 SEC **
'*** FOR EACH 1 SECOND OF REAL TIME LOOP OPERATIONS (used to emulate **
'*** coding transmission time, track switch transition time, time   ***
'*** release of electric locks and signal running time)             ***
'**********************************************************************
NUMDL = 150
T1& = TIMER                     'Update integer T1 to current time
IF T1& <> T1SAVE& THEN          'If 1 second has elapsed then...
   FOR NN = 1 TO NUMDL              '..... loop through all delays and ...
     IF TD(NN) > 0 THEN             '... if delay is active...
      TD(NN) = TD(NN) - 1            '... decrement delay by 1 second...
      IF TD(NN) = 0 THEN TD(NN) = -1 '... if timer expired set to -1, shows complete
     END IF
'testing   
'LOCATE 5, 15: PRINT "T1& "; : PRINT T1&; : PRINT "T1Save& "; : PRINT T1SAVE&
   NEXT NN                      ' After all timers have been checked....
   T1SAVE& = T1&                ' ...set saved values of time to current time..
 END IF                         '... for next Real Time Loop cycle and ....
'testing
'LOCATE 2, 18: PRINT "  td "; : PRINT TD(4)
' testing
'LOCATE 5, 1: PRINT "T1SAVE& after loop "; : PRINT T1SAVE&

END SUB                        ' return to calling program.

SUB TXPACK
  REM***************************************************
  REM**                ***TXPACK***                   **
  REM**************QB4.5 CALL VERSION*******************
  REM** SUBROUTINE TO TRANSMIT PACKET FROM PC TO NODE **
  REM**   for use with USIC, SUSIC and SMINI nodes    **
  REM***************************************************
  REM**FORM PACKET TO SEND TO USIC, SUSIC OR SMINI
     TB(1) = 255              'Set 1st start byte to all 1's
     TB(2) = 255              'Set 2nd start byte to all 1's
     TB(3) = 2                'Define start-of-text (STX = 2)
     TB(4) = UA + 65          'Add 65 offset to USIC address
     TB(5) = MT               'Define message type
     TP = 6                   'Define next position for transmit pointer
     IF MT = 80 THEN GOTO ENDMSG   'Poll request so branch to end message

  REM**LOOP TO SET UP OUTPUT DATA IN TRANSMIT BUFFER INCLUDING THE...
          '...ADDING IN OF DLE BYTES WHERE NEEDED
     FOR I = 1 TO LM    'Loop to set up output data...
                        '...including DLE processing
        IF OB(I) = 2 THEN TB(TP) = 16: TP = TP + 1: GOTO DATABYT
        IF OB(I) = 3 THEN TB(TP) = 16: TP = TP + 1: GOTO DATABYT
        IF OB(I) = 16 THEN TB(TP) = 16: TP = TP + 1
DATABYT:
        TB(TP) = OB(I)      'Move actual data byte to transmit buffer
        TP = TP + 1         'Increment pointer to next byte position
     NEXT I

  REM**END MESSAGE FORMULATION WITH End-of-text
ENDMSG:
     TB(TP) = 3  'Add end-of-text (ETX = 3)

  REM**TRANSMIT PACKET TO USIC, SUSIC OR SMINI
     FOR I = 1 TO TP       'Loop through transmit buffer to transmit

EMTY:   LSR = INP(PA + 5)      'Read UART's line status register (LSR) and...
 IF (LSR AND 32) = 0 THEN GOTO EMTY         '...if transmit holding...
                               '...register is full (bit 5 in LSR is clear)...
                               '...then branch back to wait for register to empty
        OUT PA, TB(I)  'Transmit holding register is empty so can...
                       'transmit byte out the serial port PA
         
        'PRINT TB(I);  '!!!!Optional printout of transmitted byte for...
                       '...test and debug. Note: Invoking this print...
                       '...slows PC significantly so will most likely...
                       '...need to significantly increase USIC delay (DL)
                       '...between each byte
     NEXT I    'Increment to pick up next output byte
               'Transmission of output byte is complete so execute return
END SUB

SUB WRITERR

REM PACK SUSIC1 DeCoursey Yard
                ' CARD #1, 4 outputs

               OB(1) = SM(101)
               OB(1) = SM(102) * B2 OR OB(1)
               OB(1) = SM(103) * B4 OR OB(1)
               OB(1) = SM(104) * B6 OR OB(1)

               OB(2) = SM(105)
               OB(2) = SM(106) * B2 OR OB(2)
               OB(2) = SM(107) * B4 OR OB(2)
               OB(2) = SM(108) * B6 OR OB(2)

               OB(3) = SM(109)
               OB(3) = SM(110) * B2 OR OB(3)
               OB(3) = SM(111) * B4 OR OB(3)
               OB(3) = SM(112) * B6 OR OB(3)

               OB(4) = SM(113)
               OB(4) = SM(114) * B2 OR OB(4)
               OB(4) = SM(67) * B4 OR OB(4)
               OB(4) = SM(69) * B6 OR OB(4)

                ' CARD #3, 4 outputs
               OB(5) = LED(101)                         'PORT A
               OB(5) = LED(102) * B2 OR OB(5)
               OB(5) = LED(103) * B4 OR OB(5)
               OB(5) = LED(104) * B6 OR OB(5)

               OB(6) = LED(105)                         ' PORT B
               OB(6) = LED(106) * B2 OR OB(6)
               OB(6) = LED(107) * B4 OR OB(6)
               OB(6) = LED(108) * B6 OR OB(6)

               OB(7) = LED(109)
               OB(7) = LED(110) * B2 OR OB(7)
               OB(7) = LED(111) * B4 OR OB(7)
               OB(7) = LED(112) * B6 OR OB(7)

               OB(8) = LED(113)
               OB(8) = LED(114) * B2 OR OB(8)
               OB(8) = LED(115) * B4 OR OB(8)
               OB(8) = LED(116) * B6 OR OB(8)

                ' CARD #5, 2 outputs
               OB(9) = LED(117)
               OB(9) = LED(118) * B1 OR OB(9)
               OB(9) = LED(119) * B2 OR OB(9)
               OB(9) = LED(120) * B3 OR OB(9)
               OB(9) = LED(121) * B4 OR OB(9)
               OB(9) = Light(1) * B5 OR OB(9)
               OB(9) = LED(67) * B6 OR OB(9)
               'OB(9) = LED(34) * B7 OR OB(9)
                                  
               OB(10) = Relay(1)
               OB(10) = Relay(2) * B1 OR OB(10)
               OB(10) = Relay(3) * B2 OR OB(10)
               OB(10) = Relay(4) * B3 OR OB(10)
               OB(10) = Relay(5) * B4 OR OB(10)
               OB(10) = Relay(6) * B5 OR OB(10)
               OB(10) = Relay(7) * B6 OR OB(10)
               'OB(10) = LED(67)

               'OB(11) = LED(118) * B1 OR OB(11)


                ' CARD #7, 0 outputs

  IF Diagnose$ = "I" THEN
   LOCATE 8, 1: PRINT "SUSIC#1 OUTPUT BYTES CARD 1 =";
   PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2);
   PRINT USING "####"; OB(3); : PRINT USING "####"; OB(4);
   PRINT " CARD 3 =";
   PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
   PRINT USING "####"; OB(7); : PRINT USING "####"; OB(8)
   LOCATE 9, 1: PRINT "SUSIC#1 OUTPUT BYTES CARD 5 =";
   PRINT USING "####"; OB(9); : PRINT USING "####"; OB(10);
   PRINT USING "####"; OB(11); : PRINT USING "####"; OB(12);
   PRINT " CARD 7 =";
   PRINT USING "####"; OB(13); : PRINT USING "####"; OB(14);
   PRINT USING "####"; OB(15); : PRINT USING "####"; OB(16);
  END IF

               UA = 16: NI = 16: NO = 16: REM NS = 4: CT(1) = 255
               CALL OUTPUTS

REM PACK SMINI#1 SWITCH MOTORS & SIGNALS for Walton
               OB(1) = SM(53)
               OB(1) = SM(51) * B2 OR OB(1)
               OB(1) = SM(49) * B4 OR OB(1)
               OB(1) = SM(47) * B6 OR OB(1)
               
               OB(2) = SM(37): 'N Worthville. It was a short wire run over the isle.
               OB(2) = SIGL(49) * B2 OR OB(2): ' swapped 48 & 49 here Mark wired backwards
               OB(2) = SIGL(48) * B5 OR OB(2)
               
               OB(3) = SIGR(48)
               OB(3) = LED(49) * B6 OR OB(3)
               OB(3) = LED(47) * B7 OR OB(3)

               OB(4) = SIGL(54)
               OB(4) = LED(53) * B6 OR OB(4)
               OB(4) = LED(51) * B7 OR OB(4)

               OB(5) = SIGR(54)
               OB(5) = SIGR(55) * B3 OR OB(5)
               OB(5) = LED(37) * B6 OR OB(5)
               
               OB(6) = 0

                              
               UA = 1: NI = 3: NO = 6: REM NS = 4: CT(1) = 255

               CALL OUTPUTS

REM**DISPLAY OUTPUT BYTES ON MONITOR SCREEN
 IF Diagnose$ = "I" THEN
  LOCATE 10, 36: PRINT "OUT BYTES =";
  PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
  PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
 END IF

REM PACK SMINI#2 SWITCH MOTORS & SIGNALS for Sparta
               OB(1) = SM(45)
               OB(1) = SM(43) * B2 OR OB(1)
               OB(1) = SM(41) * B4 OR OB(1)
               OB(1) = SM(39) * B6 OR OB(1)

               OB(2) = SIGR(40)
               
               OB(3) = SIGL(40)
               OB(3) = SIGL(41) * B3 OR OB(3)
               OB(3) = LED(41) * B6 OR OB(3)
               OB(3) = LED(39) * B7 OR OB(3)

               OB(4) = SIGR(46)
               OB(4) = SIGR(44) * B3 OR OB(4)
               OB(4) = LED(43) * B6 OR OB(4)
               OB(4) = LED(45) * B7 OR OB(4)

               OB(5) = SIGR(42)
               OB(5) = SIGL(42) * B3 OR OB(5)
               OB(5) = 0 * B6 OR OB(5)
               OB(5) = 0 * B7 OR OB(5)
               

               OB(6) = SIGL(46)

               UA = 2: NI = 3: NO = 6: REM NS = 4: CT(1) = 255

               CALL OUTPUTS

REM**DISPLAY OUTPUT BYTES ON MONITOR SCREEN
 IF Diagnose$ = "I" THEN
  LOCATE 11, 36: PRINT "OUT BYTES =";
  PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
  PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
 END IF

REM PACK SMINI#3 SWITCH MOTORS & SIGNALS for N Worthville
               OB(1) = SM(35)
               OB(1) = SM(33) * B2 OR OB(1)
               OB(1) = SM(31) * B4 OR OB(1)
               OB(1) = SM(29) * B6 OR OB(1)

               OB(2) = SIGL(32)
               OB(2) = SIGL(34) * B4 OR OB(2)
               
               OB(3) = 0: ' a variable here
               'OB(3) = 0 * B1 OR OB(3)
               'OB(3) = 0 * B2 OR OB(3)
               'OB(3) = 0 * B3 OR OB(3)
               'OB(3) = 0 * B4 OR OB(3)
               'OB(3) = 0 * B5 OR OB(3)
               'OB(3) = 0 * B6 OR OB(3)
               'OB(3) = 0 * B7 OR OB(3)

               OB(4) = 0: ' a variable here
               OB(4) = 0 * B1 OR OB(4)
               OB(4) = 0 * B2 OR OB(4)
               OB(4) = 0 * B3 OR OB(4)
               OB(4) = 0 * B4 OR OB(4)
               OB(4) = SIGR(34) * B5 OR OB(4)
               
               OB(5) = SIGL(30)
               OB(5) = LED(35) * B6 OR OB(5)
               OB(5) = LED(33) * B7 OR OB(5)

               OB(6) = LED(31)
               OB(6) = LED(29) * B1 OR OB(6)
               OB(6) = SIGL(31) * B2 OR OB(6)
               OB(6) = SIGL(29) * B5 OR OB(6)
               
               UA = 3: NI = 3: NO = 6: REM NS = 4: CT(1) = 255
               CALL OUTPUTS

REM**DISPLAY OUTPUT BYTES ON MONITOR SCREEN
 IF Diagnose$ = "I" THEN
  LOCATE 12, 36: PRINT "OUT BYTES =";
  PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
  PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
 END IF

REM PACK SMINI#4 SWITCH MOTORS & SIGNALS for S Worthville & Helix
               OB(1) = SIGR(32)
               OB(1) = CrossBuck(5) * B6 OR OB(1)

               OB(2) = SIGR(38)
               OB(2) = SIGR(39) * B3 OR OB(2)
               OB(2) = Bell(5) * B6 OR OB(2)
               OB(2) = Bell(5) * B7 OR OB(2)
               
               OB(3) = SIGL(38)
               OB(3) = 0 * B6 OR OB(3)
               
               OB(4) = SIGR(30): 'double head S Wortrville
               'OB(4) = 0 * B6 OR OB(4)

               OB(5) = SIGR(10) 'dwarf off CRR later rename this SIGR(30) when signals renumbered
               OB(5) = SIGR(36) * B3 OR OB(5)
               'OB(5) = 0

               OB(6) = SIGL(36)
               'OB(6) = 0

               UA = 4: NI = 3: NO = 6: REM NS = 4: CT(1) = 255
               CALL OUTPUTS


REM**DISPLAY OUTPUT BYTES ON MONITOR SCREEN
 IF Diagnose$ = "I" THEN
  LOCATE 13, 36: PRINT "OUT BYTES =";
  PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
  PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
 END IF

REM PACK SMINI#5 SWITCH MOTORS & SIGNALS for N Latonia

               OB(1) = SM(65)
               OB(1) = SM(127) * B2 OR OB(1)
               OB(1) = SM(128) * B4 OR OB(1)
               OB(1) = SM(129) * B6 OR OB(1)

               OB(2) = SM(130)
               OB(2) = SM(131) * B2 OR OB(2)
               OB(2) = SM(63) * B4 OR OB(2)
               OB(2) = SM(59) * B6 OR OB(2): ' crossover

               OB(3) = SM(61): ' Switch Lock
               OB(3) = SIGL(58) * B2 OR OB(3)
               
                             
               OB(4) = SIGR(62)
               OB(4) = SIGR(63) * B3 OR OB(4)
               OB(4) = LED(55) * B6 OR OB(4)

               OB(5) = SIGL(62)
               
               OB(6) = SIGL(60)
               OB(6) = SIGR(61) * B3 OR OB(6)
               OB(6) = LED(59) * B6 OR OB(6)
               OB(6) = LED(61) * B7 OR OB(6)

               UA = 5: NI = 3: NO = 6: REM NS = 4: CT(1) = 255
               CALL OUTPUTS


REM**DISPLAY OUTPUT BYTES ON MONITOR SCREEN
 IF Diagnose$ = "I" THEN
  LOCATE 14, 36: PRINT "OUT BYTES =";
  PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
  PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
 END IF

REM PACK SMINI#6 SWITCH MOTORS & SIGNALS for S Latonia

               OB(1) = SM(139)
               OB(1) = SM(140) * B2 OR OB(1)
               OB(1) = SM(141) * B4 OR OB(1)
               OB(1) = SM(142) * B6 OR OB(1)

               OB(2) = SM(57)
               OB(2) = SM(55) * B2 OR OB(2)
               OB(2) = SM(17) * B4 OR OB(2)
               OB(2) = SM(19) * B6 OR OB(2)

               OB(3) = SIGL(55):
               OB(3) = SIGL(56) * B3 OR OB(3)
               OB(3) = SM(21) * B6 OR OB(3)

               OB(4) = SIGL(57): ' 3 bits
               OB(4) = SIGR(58) * B3 OR OB(4)
               OB(4) = LED(17) * B6 OR OB(4)
               OB(4) = LED(19) * B7 OR OB(4)

               OB(5) = SIGR(60): '6 bits
               OB(5) = LED(21) * B6 OR OB(5)

               OB(6) = SIGR(56):  ' 8 BITS 3 HEAD SIGNAL

               UA = 6: NI = 3: NO = 6
               CALL OUTPUTS

REM**DISPLAY OUTPUT BYTES ON MONITOR SCREEN
 IF Diagnose$ = "I" THEN
  LOCATE 15, 36: PRINT "OUT BYTES =";
  PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
  PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
 END IF

REM PACK SMINI#7 SWITCH MOTORS & SIGNALS for N Campbellsburg

               OB(1) = SM(27)
               OB(1) = SM(25) * B2 OR OB(1)
               OB(1) = SM(23) * B4 OR OB(1)

               OB(2) = SIGL(24): ' DOUBEL HEAD 6 BITS

               OB(3) = SIGL(20)

               OB(4) = SIGL(28)
               
               OB(5) = SIGR(28)
               OB(5) = LED(25) * B6 OR OB(5)
               OB(5) = LED(27) * B7 OR OB(5)

               OB(6) = SIGR(26)
               OB(6) = SIGL(22) * B3 OR OB(6)
               OB(6) = LED(23) * B7 OR OB(6)

               UA = 7: NI = 3: NO = 6
               CALL OUTPUTS

REM**DISPLAY OUTPUT BYTES ON MONITOR SCREEN
 IF Diagnose$ = "I" THEN
  LOCATE 16, 36: PRINT "OUT BYTES =";
  PRINT USING "####"; OB(1); : PRINT USING "####"; OB(2); : PRINT USING "####"; OB(3);
  PRINT USING "####"; OB(4); : PRINT USING "####"; OB(5); : PRINT USING "####"; OB(6);
 END IF


END SUB

