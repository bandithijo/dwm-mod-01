/* See LICENSE file for copyright and license details. */

/* appearance */
static const unsigned int borderpx  = 1;        /* border pixel of windows */
static const int gappx              = 4;        /* gaps between windows */
static const unsigned int snap      = 5;        /* snap pixel */
static const int showbar            = 1;        /* 0 means no bar */
static const int topbar             = 1;        /* 0 means bottom bar */
static const int focusonwheel       = 0;
static const int maxnmaster         = 4;        /* define limit number of nmaster */
static const int warpcursorposition = 0;        /* 0 means center, 1 means bottom right, 2 means bottom center */
static const char *fonts[]          = {
    "JetBrainsMono Nerd Font Bandit:style=Medium:size=8",
    "Font Awesome 5 Brands:style=Regular:size=8",
    "octicons:style=Medium:size=8"
};
static char normbgcolor[]           = "#1e1e1e";
static char normbordercolor[]       = "#444444";
static char normfgcolor[]           = "#bbbbbb";
static char selfgcolor[]            = "#eeeeee";
static char selbordercolor[]        = "#005f87";
static char selbgcolor[]            = "#005f87";
static char *colors[][3]            = {
       /*               fg           bg           border   */
       [SchemeNorm] = { normfgcolor, normbgcolor, normbordercolor },
       [SchemeSel]  = { selfgcolor,  selbgcolor,  selbordercolor  },
};

/* tagging */
static const char *tags[] = { "1", "2", "3", "4", "5", "6", "7", "8", "9", "0" };

static const Rule rules[] = {
    /* xprop(1):
     *	WM_CLASS(STRING) = instance, class
     *	WM_NAME(STRING)  = title
     */
    /* class                  instance              title                         tags mask      iscentered    isfloating   monitor */
    /* Non FLoating */
    { "Gimp-2.10",            NULL,                 NULL,                         0,             0,            0,           -1 },
    { "firefox",              NULL,                 NULL,                         2,             0,            0,           -1 },
    { "qutebrowser",          NULL,                 NULL,                         2,             0,            0,           -1 },
    { "Chromium-browser",     NULL,                 NULL,                         2,             0,            0,           -1 },
    { "Google-chrome",        NULL,                 NULL,                         2,             0,            0,           -1 },
    { "TelegramDesktop",      NULL,                 NULL,                         1 << 7,        0,            0,           -1 },
    { "discord",              NULL,                 NULL,                         1 << 7,        0,            0,           -1 },
    { "Thunderbird",          NULL,                 NULL,                         1 << 6,        0,            0,           -1 },
    { "Hexchat",              NULL,                 NULL,                         1 << 5,        0,            0,           -1 },
    { "mpv",                  NULL,                 NULL,                         0,             0,            0,           -1 },
    { NULL,                   "libreoffice",        NULL,                         0,             0,            0,           -1 },
    { "Thunar",               "thunar",             NULL,                         1 << 2,        0,            0,           -1 },
    { "Org.gnome.Nautilus",   NULL,                 NULL,                         1 << 2,        0,            0,           -1 },
    { "St",                   NULL,                 "NeoMutt",                    1 << 6,        0,            0,           -1 },
    { "St",                   NULL,                 "Ranger",                     0,             0,            0,           -1 },
    { "St",                   NULL,                 "Newsboat",                   1 << 5,        0,            0,           -1 },
    { "St",                   NULL,                 "WeeChat",                    1 << 5,        0,            0,           -1 },
    { "Transmission-gtk",     NULL,                 NULL,                         1 << 4,        0,            0,           -1 },
    { "Postbird",             NULL,                 NULL,                         0,             0,            0,           -1 },
    { "xdman-Main",           NULL,                 "XDM 2020",                   0,             0,            0,           -1 },
    { "Guvcview",             NULL,                 NULL,                         1 << 4,        0,            0,           -1 },
    { "winword.exe",          NULL,                 NULL,                         0,             0,            0,           -1 },
    { "calibre",              NULL,                 NULL,                         0,             1,            0,           -1 },
    { "Soffice",              "soffice",            NULL,                         0,             0,            0,            0 },
    { "Soffice",              "soffice",            "Presenting: ",               0,             0,            0,            1 },
    { "Postman",              NULL,                 NULL,                         0,             0,            0,            1 },
    /* class                  instance              title                         tags mask      iscentered    isfloating   monitor */
    /* Floating */
    { "TelegramDesktop",      NULL,                 "Media viewer",               1 << 7,        1,            1,           -1 },
    { "Tor Browser",          "Navigator",          NULL,                         2,             1,            1,           -1 },
    { "St",                   NULL,                 "st+",                        0,             1,            1,           -1 },
    { "St",                   NULL,                 "st+:",                       0,             0,            1,           -1 },
    { "Arandr",               NULL,                 NULL,                         0,             1,            1,           -1 },
    { "Gcolor3",              NULL,                 "Color Picker",               0,             0,            1,           -1 },
    { "Gcolor3",              NULL,                 "Color picker",               0,             0,            1,           -1 },
    { "Gnome-calculator",     NULL,                 "Calculator",                 0,             0,            1,           -1 },
    { "Hexchat",              NULL,                 "Network List - HexChat",     1 << 5,        1,            1,           -1 },
    { "SimpleScreenRecorder", NULL,                 NULL,                         0,             1,            1,           -1 },
    { "Soffice",              NULL,                 "Print",                      0,             1,            1,           -1 },
    { "Chrome",               NULL,                 "Save File",                  2,             0,            1,           -1 },
    { "Barrier",              NULL,                 NULL,                         1 << 4,        0,            1,           -1 },
    { "Soffice",              "soffice",            NULL,                         0,             0,            0,           -1 },
    { "Thunar",               "thunar",             "File Operation Progress",    0,             0,            1,           -1 },
    { "System-config-printer.py", NULL,             NULL,                         0,             1,            1,           -1 },
    { "Nm-connection-editor", NULL,                 "Network Connections",        0,             0,            1,           -1 },
    { "Pavucontrol",          NULL,                 NULL,                         0,             1,            1,           -1 },
    { "Gpick",                NULL,                 NULL,                         0,             0,            1,           -1 },
    { "vokoscreen",           NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Blueman-manager",      NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Xsane",                NULL,                 "No devices available",       0,             0,            1,           -1 },
    { "scrcpy",               NULL,                 NULL,                         0,             0,            1,           -1 },
    { "GParted",              NULL,                 NULL,                         0,             1,            1,           -1 },
    { "zoom",                 NULL,                 "Question and Answer",        0,             0,            1,           -1 },
    { "zoom",                 NULL,                 "as_toolbar",                 0,             0,            1,           -1 },
    { "guvcview",             NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Key-mon",              NULL,                 NULL,                         0,             1,            1,           -1 },
    { "Gnome-power-statistics", NULL,               NULL,                         0,             1,            1,           -1 },
    { "firefox",              "Browser",            "About Mozilla Firefox",      0,             0,            1,           -1 },
    { "Tor Browser",          "Browser",            "About Tor Browser",          0,             0,            1,           -1 },
    { "xdman-Main",           NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Gkamus",               NULL,                 NULL,                         0,             1,            1,           -1 },
    { "Kamus",                NULL,                 NULL,                         0,             1,            1,           -1 },
    { "KBBI-Qt",              NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Pysheng-gui",          NULL,                 NULL,                         0,             0,            1,           -1 },
    { "qtqr",                 NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Mainwindow.py",        NULL,                 "PlayOnLinux",                0,             0,            1,           -1 },
    { "ffplay",               NULL,                 NULL,                         0,             0,            1,           -1 },
    { NULL,                   NULL,                 "xzoom x2",                   0,             0,            1,           -1 },
    { "Crow Translate",       NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Dragon-drag-and-drop", NULL,                 NULL,                         0,             1,            1,           -1 },
    { "Colorgrab",            NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Pidgin",               NULL,                 NULL,                         0,             0,            1,           -1 },
    { "Pidgin",               NULL,                 "Buddy List",                 0,             0,            1,           -1 },
    { "Wihotspot-gui",        NULL,                 "Wi Hotspot",                 0,             0,            1,           -1 },
    { "Polkit-mate-authentication-agent-1", NULL,   "Authenticate",               0,             1,            1,           -1 },
    { "Soundconverter",       "Soundconverter",     "SoundConverter",             0,             1,            1,           -1 },
    { "mpv",                  "gl",                 NULL,                         0,             1,            1,           -1 },
    { "TelegramDesktop",      "telegram-desktop",   "MARPEL",                     0,             1,            1,           -1 },
    { "Gcr-prompter",         "gcr-prompter",       NULL,                         0,             1,            1,           -1 },
    { "winbox64.exe",         NULL,                 NULL,                         0,             1,            1,           -1 },
    /* class                  instance              title                         tags mask      iscentered    isfloating   monitor */
    /* Scratchpad */
    { NULL,                   NULL,                 "hidden",               scratchpad_mask,     0,            1,           -1 },
};

/* layout(s) */
static const float mfact     = 0.50; /* factor of master area size [0.05..0.95] */
static const int nmaster     = 1;    /* number of clients in master area */
static const int resizehints = 0;    /* 1 means respect size hints in tiled resizals */

#include "fibonacci.c"
static const Layout layouts[] = {
	/* symbol     arrange function */
	{ "[]=",      tile },    /* first entry is default */
	{ "><>",      NULL },    /* no layout function means floating behavior */
	{ "[M]",      monocle },
	{ "TTT",      bstack },
	{ "===",      bstackhoriz },
 	{ "[@]",      spiral },
 	{ "[\\]",     dwindle },
	{ "|M|",      centeredmaster },
	{ ">M>",      centeredfloatingmaster },
};

/* key definitions */
#define MODKEY Mod4Mask
#define TAGKEYS(KEY,TAG) \
	{ MODKEY,                       KEY,      view,           {.ui = 1 << TAG} }, \
	{ MODKEY|ControlMask,           KEY,      toggleview,     {.ui = 1 << TAG} }, \
	{ MODKEY|ShiftMask,             KEY,      tag,            {.ui = 1 << TAG} }, \
	{ MODKEY|ControlMask|ShiftMask, KEY,      toggletag,      {.ui = 1 << TAG} },

/* helper for spawning shell commands in the pre dwm-5.0 fashion */
#define SHCMD(cmd) { .v = (const char*[]){ "/bin/sh", "-c", cmd, NULL } }

/* commands */
static const char *termcmd[]  = { "st", NULL };

#include "movestack.c"
static Key keys[] = {
	/* modifier                     key        function        argument */
	{ MODKEY,                       XK_d,      spawn,             SHCMD("/usr/bin/dmenu-apps") },
	{ MODKEY|ShiftMask,             XK_Return, spawn,             {.v = termcmd } },
    { MODKEY,                       XK_b,      togglebar,         {0} },
	{ MODKEY,                       XK_j,      focusstack,        {.i = +1 } },
	{ MODKEY,                       XK_k,      focusstack,        {.i = -1 } },
	{ MODKEY,                       XK_i,      incnmaster,        {.i = +1 } },
	{ MODKEY|ShiftMask,             XK_i,      incnmaster,        {.i = -1 } },
	{ MODKEY,                       XK_h,      setmfact,          {.f = -0.001} },
	{ MODKEY,                       XK_l,      setmfact,          {.f = +0.001} },
	{ MODKEY|ShiftMask,             XK_h,      setmfact,          {.f = -0.01} },
	{ MODKEY|ShiftMask,             XK_l,      setmfact,          {.f = +0.01} },
	{ MODKEY|ControlMask,           XK_h,      setcfact,          {.f = +0.01} },
	{ MODKEY|ShiftMask|ControlMask, XK_h,      setcfact,          {.f = +0.1} },
	{ MODKEY|ShiftMask|ControlMask, XK_l,      setcfact,          {.f = -0.1} },
	{ MODKEY|ControlMask,           XK_l,      setcfact,          {.f = -0.01} },
	{ MODKEY|ControlMask,           XK_o,      setcfact,          {.f =  0.00} },
	{ MODKEY|ShiftMask,             XK_j,      movestack,         {.i = +1 } },
	{ MODKEY|ShiftMask,             XK_k,      movestack,         {.i = -1 } },
	{ MODKEY|ShiftMask,             XK_o,      resetlayout,       {0} },
	{ MODKEY,                       XK_Return, zoom,              {0} },
	{ MODKEY,                       XK_Tab,    view,              {0} },
	{ MODKEY|ShiftMask,             XK_c,      killclient,        {0} },
	{ MODKEY,                       XK_t,      setlayout,         {.v = &layouts[0]} },
	{ MODKEY,                       XK_f,      setlayout,         {.v = &layouts[1]} },
	{ MODKEY,                       XK_m,      setlayout,         {.v = &layouts[2]} },
	{ MODKEY|ShiftMask,             XK_t,      setlayout,         {.v = &layouts[3]} },
	{ MODKEY|ControlMask,           XK_t,      setlayout,         {.v = &layouts[4]} },
	{ MODKEY,                       XK_r,      setlayout,         {.v = &layouts[5]} },
	{ MODKEY|ShiftMask,             XK_r,      setlayout,         {.v = &layouts[6]} },
	{ MODKEY|ShiftMask,             XK_m,      setlayout,         {.v = &layouts[7]} },
	{ MODKEY|ControlMask,           XK_m,      setlayout,         {.v = &layouts[8]} },
	{ MODKEY,                       XK_space,  setlayout,         {0} },
	{ MODKEY|ShiftMask,             XK_space,  togglefloating,    {0} },
	{ MODKEY|ShiftMask,             XK_f,      togglefullscr,     {0} },
	{ MODKEY,                       XK_s,      togglesticky,      {0} },
    { MODKEY|ShiftMask,             XK_s,      togglecanfocusfloating, {0} },
	{ MODKEY,                       XK_comma,  focusmon,          {.i = -1 } },
	{ MODKEY,                       XK_period, focusmon,          {.i = +1 } },
	{ MODKEY|ShiftMask,             XK_comma,  tagmon,            {.i = -1 } },
	{ MODKEY|ShiftMask,             XK_period, tagmon,            {.i = +1 } },
	{ MODKEY,                       XK_F5,     xrdb,              {.v = NULL } },
	{ MODKEY,                       0x5b,      setgaps,           {.i = -4 } },
	{ MODKEY,                       0x5d,      setgaps,           {.i = +4 } },
	{ MODKEY|ShiftMask,             XK_equal,  setgaps,           {.i = 0  } },
    { MODKEY|ControlMask,           XK_space,  focusmaster,       {0} },
	TAGKEYS(                        XK_1,                         0)
	TAGKEYS(                        XK_2,                         1)
	TAGKEYS(                        XK_3,                         2)
	TAGKEYS(                        XK_4,                         3)
	TAGKEYS(                        XK_5,                         4)
	TAGKEYS(                        XK_6,                         5)
	TAGKEYS(                        XK_7,                         6)
	TAGKEYS(                        XK_8,                         7)
	TAGKEYS(                        XK_9,                         8)
	TAGKEYS(                        XK_0,                         9)
	{ MODKEY|ShiftMask,             XK_q,      quit,              {0} },
	{ MODKEY,                       XK_minus,  scratchpad_show,   {0} },
	{ MODKEY|ShiftMask,             XK_minus,  scratchpad_hide,   {0} },
	{ MODKEY|ControlMask,           XK_minus,  scratchpad_remove, {0} },
	{ MODKEY|Mod1Mask|ShiftMask,    XK_Down,   aspectresize,      {.i = +10} },
	{ MODKEY|Mod1Mask|ShiftMask,    XK_Up,     aspectresize,      {.i = -10} },
	{ MODKEY|ShiftMask,             XK_Down,   moveresize,        {.v = "  0x  10y   0w   0h" } },
	{ MODKEY|ShiftMask,             XK_Up,     moveresize,        {.v = "  0x -10y   0w   0h" } },
	{ MODKEY|ShiftMask,             XK_Right,  moveresize,        {.v = " 10x   0y   0w   0h" } },
	{ MODKEY|ShiftMask,             XK_Left,   moveresize,        {.v = "-10x   0y   0w   0h" } },
	{ MODKEY,                       XK_Down,   moveresize,        {.v = "  0x   1y   0w   0h" } },
	{ MODKEY,                       XK_Up,     moveresize,        {.v = "  0x  -1y   0w   0h" } },
	{ MODKEY,                       XK_Right,  moveresize,        {.v = "  1x   0y   0w   0h" } },
	{ MODKEY,                       XK_Left,   moveresize,        {.v = " -1x   0y   0w   0h" } },
	{ MODKEY|Mod1Mask,              XK_Down,   moveresize,        {.v = "  0x   0y   0w  10h" } },
	{ MODKEY|Mod1Mask,              XK_Up,     moveresize,        {.v = "  0x   0y   0w -10h" } },
	{ MODKEY|Mod1Mask,              XK_Right,  moveresize,        {.v = "  0x   0y  10w   0h" } },
	{ MODKEY|Mod1Mask,              XK_Left,   moveresize,        {.v = "  0x   0y -10w   0h" } },
    { MODKEY|ControlMask,           XK_Up,     movethrow,         {.ui = DIR_N  }},
    { MODKEY|ControlMask,           XK_Down,   movethrow,         {.ui = DIR_S  }},
    { MODKEY|ControlMask,           XK_Left,   movethrow,         {.ui = DIR_W  }},
    { MODKEY|ControlMask,           XK_Right,  movethrow,         {.ui = DIR_E  }},
    { MODKEY|ControlMask,           XK_g,      movethrow,         {.ui = DIR_C  }},

    // Custom Keys
    /* I have migrated all this custom keys with SXHKD */
};

/* button definitions */
/* click can be ClkTagBar, ClkLtSymbol, ClkStatusText, ClkWinTitle, ClkClientWin, or ClkRootWin */
static Button buttons[] = {
	/* click                event mask        button          function        argument */
	{ ClkLtSymbol,          0,                Button1,        setlayout,      {0} },
	{ ClkLtSymbol,          0,                Button3,        setlayout,      {.v = &layouts[2]} },
	{ ClkWinTitle,          0,                Button2,        zoom,           {0} },
	{ ClkStatusText,        0,                Button2,        spawn,          {.v = termcmd } },
	{ ClkClientWin,         MODKEY,           Button1,        movemouse,      {0} },
	{ ClkClientWin,         MODKEY,           Button2,        togglefloating, {0} },
	{ ClkClientWin,         MODKEY,           Button3,        resizemouse,    {0} },
	{ ClkClientWin,         MODKEY|ShiftMask, Button3,        dragcfact,      {0} },
	{ ClkTagBar,            0,                Button1,        view,           {0} },
	{ ClkTagBar,            0,                Button3,        toggleview,     {0} },
	{ ClkTagBar,            MODKEY,           Button1,        tag,            {0} },
	{ ClkTagBar,            MODKEY,           Button3,        toggletag,      {0} },
};

void
setlayoutex(const Arg *arg)
{
	setlayout(&((Arg) { .v = &layouts[arg->i] }));
}

void
viewex(const Arg *arg)
{
	view(&((Arg) { .ui = 1 << arg->ui }));
}

void
viewall(const Arg *arg)
{
	view(&((Arg){.ui = ~0}));
}

void
toggleviewex(const Arg *arg)
{
	toggleview(&((Arg) { .ui = 1 << arg->ui }));
}

void
tagex(const Arg *arg)
{
	tag(&((Arg) { .ui = 1 << arg->ui }));
}

void
toggletagex(const Arg *arg)
{
	toggletag(&((Arg) { .ui = 1 << arg->ui }));
}

void
tagall(const Arg *arg)
{
	tag(&((Arg){.ui = ~0}));
}

/* signal definitions */
/* signum must be greater than 0 */
/* trigger signals using `xsetroot -name "fsignal:<signame> [<type> <value>]"` */
static Signal signals[] = {
	/* signum           function */
	{ "focusstack",     focusstack },
	{ "setmfact",       setmfact },
	{ "togglebar",      togglebar },
	{ "incnmaster",     incnmaster },
	{ "togglefloating", togglefloating },
	{ "focusmon",       focusmon },
	{ "tagmon",         tagmon },
	{ "zoom",           zoom },
	{ "view",           view },
	{ "viewall",        viewall },
	{ "viewex",         viewex },
	{ "toggleview",     view },
	{ "toggleviewex",   toggleviewex },
	{ "tag",            tag },
	{ "tagall",         tagall },
	{ "tagex",          tagex },
	{ "toggletag",      tag },
	{ "toggletagex",    toggletagex },
	{ "killclient",     killclient },
	{ "quit",           quit },
	{ "setlayout",      setlayout },
	{ "setlayoutex",    setlayoutex },
};
