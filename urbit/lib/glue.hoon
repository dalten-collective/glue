/-  *glue
/+  agentio, *sane, *mip, dbug
::
|%
++  card   card:agent:gall
++  zoom
  |=  [caz=(list card) f=$-(path path)]
  ^-  (list card)
  %+  turn  caz
  |=  =card
  ?+  -.card  card
      %pass
    card(p (f p.card))
  ::
      %give  
    ?.  ?=(?(%fact %kick) -.p.card)  card
    card(paths.p (turn paths.p.card f))
  ==
::
++  strip
  |=  =knot  |=  =path  ^-  ^path
  ?.  &(?=(^ path) =(knot -.path))  path  +.path
::
++  open
  |=  [door=vase arg=*]  ^-  vase
  door(+6.q arg)
--
::
^?
|%
+$  state  cuts=(mip desk term vase)
::
++  tool
  =|  state  ::TODO read glue/bill
  =*  state  -
  ::
  |=  =agent:gall
  %-  agent:dbug
  ^-  agent:gall
  |_  =bowl:gall
  +*  this   . 
      ag     ~(. agent bowl)
      dish   |=(=mark bowl) ::TODO dish
      io     ~(. agentio bowl)
      disk   ~(. ^disk bowl)
    ::  trans  ~(. core on-save:ag bowl)
  ::
  ++  on-init
    ^-  (quip card agent:gall)
    =^  cards  agent  on-init:ag
    [cards this]
  ::
  ++  on-save  ::TODO slop everything
    !>  :+  %glue
      on-save:ag
    %-  ~(rut bi cuts)
    |=  [=desk =term cut=vase]
    ?.  (slab %read %on-save p.cut)  ~
    `!<(vase (slap cut(+6.q [on-save:ag (dish term)]) limb/%on-save))
  ::
  ++  on-load
    |=  old=vase
    ^-  (quip card agent:gall)
    ?~  res=(mole |.(!<([%glue agent=vase cuts=(mip desk term (unit vase))] old)))
      =^  cards  agent  (on-load:ag old)
      [cards this]
    =^  cards  agent  (on-load:ag agent.u.res)
    =^  calls  cuts
      ^-  (quip call (mip desk term vase))
      %-  ~(rep by cuts.u.res)
      |=  [[=desk inner=(map term (unit vase))] acc=(quip call _cuts)]
      ^-  (quip call _cuts)
      %-  ~(rep by inner)
      |=  [[=term ole=(unit vase)] bcc=(quip call _cuts)]
      ^-  (quip call _cuts)
      =-  :-  (weld -.bcc !<((list call) (slot 2 -)))
          (~(put bi +.bcc) desk term (slot 3 -))
      =/  cut  .^(vase ca/(scry:io desk (weld cuts:disk /[term]/hoon)))
      ?.  &(?=(^ ole) (slab %read %on-load p.cut))
        (slop !>(*(list call)) cut)
      %-  slam  :_  u.ole
      (slap cut(+6.q [on-save:ag (dish term)]) limb/%on-load)
    ~&  >  loaded=(turn ~(tap bi cuts) |=([=desk =term =vase] desk^term^-:vase))
    [cards this]
  ::
  ++  on-poke
    |=  [=mark =vase]
    ^-  (quip card agent:gall)
    ?:  ?=(%glue mark)
      ~&  >>  [%glue-poke vase=vase]
      ?-  cmd=!<($%([%add =desk] [%del =desk]) vase)
          [%del *]
        `this(cuts (~(del by cuts) desk.cmd))
      ::
          [%add *]
        :-  ~[(mult-cuts:disk desk.cmd) (next-cuts:disk desk.cmd)]
        %=    this
            cuts
          %+  ~(put by cuts)  desk.cmd
          %-  my  %+  murn  (curr-cuts:disk desk.cmd)
          |=  =path
          ^-  (unit (pair term ^vase))
          ?.  ?=([@ %hoon ~] (slag (lent cuts:disk) path))  ~
          :+  ~  (snag (lent cuts:disk) path)
          .^(^vase ca/(scry:io desk.cmd path))
        ==
      ==
    ::
    =*  call-inner  
      ~&  >>  [%simple-poke vase=vase]
      =^  cards  agent  (on-poke:ag mark vase)
      [cards this]
    ::
    =/  res=(list (trel ^vase desk term))
      =>  .(mark (trip mark))
      %+  murn  (fand "-" mark)
      |=  ix=@ud
      =/  =desk  (crip (scag ix mark))
      =/  =term  (crip (slag +(ix) mark))
      (bind (~(get bi cuts) desk term) (late [desk term]))
    ?.  ?=([* ~] res)  ~&  >>  %no-cut  call-inner
    =/  [cut=^vase =desk =term]  i.res
    ?.  (slab %read %on-poke p.cut)  ~&  >>  %no-on-poke  call-inner
    ::
    ~&  >>  [%trans-poke vase=vase]
    =.  cut  cut(+6.q [on-save:ag (dish mark)])
    ~&  >>  cut-vase-type=p.cut
    =^  calls  cut
      =-  ~|  %bad-return  [!<((list call) (slot 2 -)) (slot 3 -)]
      ~|  %bad-inner
      %+  slam  
        ::  =-  ~&  >>  door-type=p.-  -  
        (slap cut limb/%on-poke)
      ::  =-  ~&  >>  arg-vase=-  -
      !>([!<(^mark (slot 2 vase)) (slot 3 vase)])
    =^  cards  agent
      %+  roll  calls
      |:  *[=call caz=(list card:agent:gall) ag=_agent]
      =-  [(weld -.- caz) +.-]
      ?:  ?=(%card -.call)  [~[card.call] ag]
      =.  ag  ag(src.+< +<.call)
      ?:  ?=(%on-init -.call)  on-init:ag
      !<  (quip card _ag)
      ?:  ?=(%on-poke -.call)
        (slam (slap !>(ag) limb/%on-poke) !>(+>.call))
      =-  ~&  >>  slammed/-:!>(-)  -
      %+  slam
        =-  ~&  >>  arm/-.call  -
        (slap !>(ag) limb/-.call)
      =-  ~&  >>  foolol/[arg-type=p.- arg=+>.call]  -
      !>(+>.call)
    :-  cards
    this(cuts (~(jab bi cuts) desk term _cut))
  ::
  ++  on-watch
    |=  =path
    ^-  (quip card agent:gall)
    !@  on-watch:core
      !!
    =^  cards  agent  (on-watch:ag path)
    [cards this]
  ::
  ++  on-agent
    |=  [=wire =sign:agent:gall]
    ^-  (quip card agent:gall)
    !@  on-agent:core
      !!
    =^  cards  agent  (on-agent:ag wire sign)
    [cards this]
  ::
  ++  on-arvo
    |=  [=wire =sign-arvo]
    ^-  (quip card agent:gall)
    !@  on-arvo:core
      !!
    =^  cards  agent  (on-arvo:ag wire sign-arvo)
    [cards this]
  ::
  ++  on-peek
    |=  =path
    ^-  (unit (unit cage))
    ?.  ?=([%x term *] path)  (on-peek:ag path)
    =*  mark  &2.path
    =*  inner  path(+ +>.path)
    ?:  ?=(%transformer mark)  ``path+!>(~(tap in ~(key by cuts)))
::    ?~  res=(~(get by cuts) mark)
    (on-peek:ag path)
::    !<  (unit (unit cage))
::    %+  slam
::      (slap vase.u.res(+6.q [on-save:ag (dish mark)]) limb/%on-peek)
::    !>(inner)
  ::
  ++  on-leave
    |=  =path
    ^-  (quip card agent:gall)
    !@  on-leave:core
      !!
    =^  cards  agent  (on-leave:ag path)
    [cards this]
  ::
  ++  on-fail
    |=  [=term =tang]
    ^-  (quip card agent:gall)
    !@  on-fail:core
      !!
    =^  cards  agent  (on-fail:ag term tang)
    [cards this]
  --
::
++  disk
  |_  =bowl:gall
  +*  io  ~(. agentio bowl)
  ++  cuts  /lib/glue/cuts
  ::
  ++  prev-aeon
    |=  =desk
    ^-  @ud
    (dec ud:.^(cass:clay cw/(scry:io desk /)))
  ::
  ++  curr-cuts
    |=  =desk
    .^((list path) ct/(scry:io desk cuts))
  ::
  ++  prev-cuts
    |=  =desk
    .^  (list path)  %ct
      (scot %p our.bowl)  desk  (scot %ud (prev-aeon desk))
      cuts
    ==
  ::
  ++  next-cuts
    |=  =desk
    ^-  card
    (~(warp-our pass:io //glue/clay/next) [desk `[%next %t da/now.bowl cuts]])
  ::
  ++  mult-cuts
    |=  =desk
    ^-  card
    %-  ~(warp-our pass:io //glue/clay/next)
    [desk `[%mult da/now.bowl (sy (turn (curr-cuts desk) (lead %a)))]]
  --
--
