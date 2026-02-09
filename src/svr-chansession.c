/*
 * Dropbear - a SSH2 server
 * 
 * Copyright (c) 2002,2003 Matt Johnston
 * All rights reserved.
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE. */

#include "includes.h"
#include "packet.h"
#include "buffer.h"
#include "session.h"
#include "dbutil.h"
#include "channel.h"
#include "chansession.h"
#include "sshpty.h"
#include "termcodes.h"
#include "ssh.h"
#include "dbrandom.h"
#include "x11fwd.h"
#include "agentfwd.h"
#include "runopts.h"
#include "auth.h"

/* Handles sessions (either shells or programs) requested by the client */

static int sessioncommand(struct Channel *channel, struct ChanSess *chansess,
		int iscmd, int issubsys);
static int sessionpty(struct ChanSess * chansess);
static int sessionsignal(const struct ChanSess *chansess);
static int noptycommand(struct Channel *channel, struct ChanSess *chansess);
static int ptycommand(struct Channel *channel, struct ChanSess *chansess);
static int sessionwinchange(const struct ChanSess *chansess);
static void execchild(const void *user_data_chansess);
static void addchildpid(struct ChanSess *chansess, pid_t pid);
static void sesssigchild_handler(int val);
static void closechansess(const struct Channel *channel);
static void cleanupchansess(const struct Channel *channel);
static int newchansess(struct Channel *channel);
static void chansessionrequest(struct Channel *channel);
static int sesscheckclose(struct Channel *channel);

static void send_exitsignalstatus(const struct Channel *channel);
static void send_msg_chansess_exitstatus(const struct Channel * channel,
		const struct ChanSess * chansess);
static void send_msg_chansess_exitsignal(const struct Channel * channel,
		const struct ChanSess * chansess);
static void get_termmodes(const struct ChanSess *chansess);

const struct ChanType svrchansess = {
	"session", /* name */
	newchansess, /* inithandler */
	sesscheckclose, /* checkclosehandler */
	chansessionrequest, /* reqhandler */
	closechansess, /* closehandler */
	cleanupchansess /* cleanup */
};

/* Returns whether the channel is ready to close. The child process
   must not be running (has never started, or has exited) */
static int sesscheckclose(struct Channel *channel) {
	struct ChanSess *chansess = (struct ChanSess*)channel->typedata;
	TRACE(("sesscheckclose, pid %d, exitpid %d", chansess->pid, chansess->exit.exitpid))

	if (chansess->exit.exitpid != -1) {
		channel->flushing = 1;
	}
	return chansess->pid == 0 || chansess->exit.exitpid != -1;
}

/* Handler for childs exiting, store the state for return to the client */

/* There's a particular race we have to watch out for: if the forked child
 * executes, exits, and this signal-handler is called, all before the parent
 * gets to run, then the childpids[] array won't have the pid in it. Hence we
 * use the svr_ses.lastexit struct to hold the exit, which is then compared by
 * the parent when it runs. This work correctly at least in the case of a
 * single shell spawned (ie the usual case) */
void svr_chansess_checksignal(void) {
	int status;
	pid_t pid;

	if (!ses.channel_signal_pending) {
		return;
	}

	while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {
		unsigned int i;
		struct exitinfo *ex = NULL;
		TRACE(("svr_chansess_checksignal : pid %d", pid))

		ex = NULL;
		/* find the corresponding chansess */
		for (i = 0; i < svr_ses.childpidsize; i++) {
			if (svr_ses.childpids[i].pid == pid) {
				TRACE(("found match session"));
				ex = &svr_ses.childpids[i].chansess->exit;
				break;
			}
		}

		/* If the pid wasn't matched, then we might have hit the race mentioned
		 * above. So we just store the info for the parent to deal with */
		if (ex == NULL) {
			TRACE(("using lastexit"));
			ex = &svr_ses.lastexit;
		}

		ex->exitpid = pid;
		if (WIFEXITED(status)) {
			ex->exitstatus = WEXITSTATUS(status);
		}
		if (WIFSIGNALED(status)) {
			ex->exitsignal = WTERMSIG(status);
#if !defined(AIX) && defined(WCOREDUMP)
			ex->exitcore = WCOREDUMP(status);
#else
			ex->exitcore = 0;
#endif
		} else {
			/* we use this to determine how pid exited */
			ex->exitsignal = -1;
		}
	}
}

static void sesssigchild_handler(int UNUSED(dummy)) {
	struct sigaction sa_chld;

	const int saved_errno = errno;

	/* Make sure that the main select() loop wakes up */
	while (1) {
		/* isserver is just a random byte to write. We can't do anything
		about an error so should just ignore it */
		if (write(ses.signal_pipe[1], &ses.isserver, 1) == 1
				|| errno != EINTR) {
			break;
		}
	}

	sa_chld.sa_handler = sesssigchild_handler;
	sa_chld.sa_flags = SA_NOCLDSTOP;
	sigemptyset(&sa_chld.sa_mask);
	sigaction(SIGCHLD, &sa_chld, NULL);

	errno = saved_errno;
}

/* send the exit status or the signal causing termination for a session */
static void send_exitsignalstatus(const struct Channel *channel) {

	struct ChanSess *chansess = (struct ChanSess*)channel->typedata;

	if (chansess->exit.exitpid >= 0) {
		if (chansess->exit.exitsignal > 0) {
			send_msg_chansess_exitsignal(channel, chansess);
		} else {
			send_msg_chansess_exitstatus(channel, chansess);
		}
	}
}

/* send the exitstatus to the client */
static void send_msg_chansess_exitstatus(const struct Channel * channel,
		const struct ChanSess * chansess) {

	dropbear_assert(chansess->exit.exitpid != -1);
	dropbear_assert(chansess->exit.exitsignal == -1);

	CHECKCLEARTOWRITE();

	buf_putbyte(ses.writepayload, SSH_MSG_CHANNEL_REQUEST);
	buf_putint(ses.writepayload, channel->remotechan);
	buf_putstring(ses.writepayload, "exit-status", 11);
	buf_putbyte(ses.writepayload, 0); /* boolean FALSE */
	buf_putint(ses.writepayload, chansess->exit.exitstatus);

	encrypt_packet();

}

/* send the signal causing the exit to the client */
static void send_msg_chansess_exitsignal(const struct Channel * channel,
		const struct ChanSess * chansess) {

	int i;
	char* signame = NULL;
	dropbear_assert(chansess->exit.exitpid != -1);
	dropbear_assert(chansess->exit.exitsignal > 0);

	TRACE(("send_msg_chansess_exitsignal %d", chansess->exit.exitsignal))

	CHECKCLEARTOWRITE();

	/* we check that we can match a signal name, otherwise
	 * don't send anything */
	for (i = 0; signames[i].name != NULL; i++) {
		if (signames[i].signal == chansess->exit.exitsignal) {
			signame = signames[i].name;
			break;
		}
	}

	if (signame == NULL) {
		return;
	}

	buf_putbyte(ses.writepayload, SSH_MSG_CHANNEL_REQUEST);
	buf_putint(ses.writepayload, channel->remotechan);
	buf_putstring(ses.writepayload, "exit-signal", 11);
	buf_putbyte(ses.writepayload, 0); /* boolean FALSE */
	buf_putstring(ses.writepayload, signame, strlen(signame));
	buf_putbyte(ses.writepayload, chansess->exit.exitcore);
	buf_putstring(ses.writepayload, "", 0); /* error msg */
	buf_putstring(ses.writepayload, "", 0); /* lang */

	encrypt_packet();
}

/* set up a session channel */
static int newchansess(struct Channel *channel) {

	struct ChanSess *chansess;

	TRACE(("new chansess %p", (void*)channel))

	dropbear_assert(channel->typedata == NULL);

	chansess = (struct ChanSess*)m_malloc(sizeof(struct ChanSess));
	chansess->cmd = NULL;
	chansess->connection_string = NULL;
	chansess->client_string = NULL;
	chansess->pid = 0;

	/* pty details */
	chansess->master = -1;
	chansess->slave = -1;
	chansess->tty = NULL;
	chansess->term = NULL;

	chansess->exit.exitpid = -1;

	channel->typedata = chansess;

#if DROPBEAR_X11FWD
	chansess->x11listener = NULL;
	chansess->x11authprot = NULL;
	chansess->x11authcookie = NULL;
#endif

#if DROPBEAR_SVR_AGENTFWD
	chansess->agentlistener = NULL;
	chansess->agentfile = NULL;
	chansess->agentdir = NULL;
#endif

	/* Will drop to DROPBEAR_PRIO_NORMAL if a non-tty command starts */
	channel->prio = DROPBEAR_PRIO_LOWDELAY;

	return 0;

}

static struct logininfo* 
chansess_login_alloc(const struct ChanSess *chansess) {
	struct logininfo * li;
	li = login_alloc_entry(chansess->pid, ses.authstate.username,
			svr_ses.remotehost, chansess->tty);
	return li;
}

/* send exit status message before the channel is closed */
static void closechansess(const struct Channel *channel) {
	struct ChanSess *chansess;

	TRACE(("enter closechansess"))

	chansess = (struct ChanSess*)channel->typedata;

	if (chansess == NULL) {
		TRACE(("leave closechansess: chansess == NULL"))
		return;
	}

	send_exitsignalstatus(channel);
	TRACE(("leave closechansess"))
}

/* clean a session channel */
static void cleanupchansess(const struct Channel *channel) {

	struct ChanSess *chansess;
	unsigned int i;
	struct logininfo *li;

	TRACE(("enter closechansess"))

	chansess = (struct ChanSess*)channel->typedata;

	if (chansess == NULL) {
		TRACE(("leave closechansess: chansess == NULL"))
		return;
	}

	m_free(chansess->cmd);
	m_free(chansess->term);
	m_free(chansess->original_command);

	if (chansess->tty) {
		/* write the utmp/wtmp login record */
		li = chansess_login_alloc(chansess);

		svr_raise_gid_utmp();
		login_logout(li);
		svr_restore_gid();

		login_free_entry(li);

		pty_release(chansess->tty);
		m_free(chansess->tty);
	}

#if DROPBEAR_X11FWD
	x11cleanup(chansess);
#endif

#if DROPBEAR_SVR_AGENTFWD
	svr_agentcleanup(chansess);
#endif

	/* clear child pid entries */
	for (i = 0; i < svr_ses.childpidsize; i++) {
		if (svr_ses.childpids[i].chansess == chansess) {
			dropbear_assert(svr_ses.childpids[i].pid > 0);
			TRACE(("closing pid %d", svr_ses.childpids[i].pid))
			TRACE(("exitpid is %d", chansess->exit.exitpid))
			svr_ses.childpids[i].pid = -1;
			svr_ses.childpids[i].chansess = NULL;
		}
	}
				
	m_free(chansess);

	TRACE(("leave closechansess"))
}

/* Handle requests for a channel. These can be execution requests,
 * or x11/authagent forwarding. These are passed to appropriate handlers */
static void chansessionrequest(struct Channel *channel) {

	char * type = NULL;
	unsigned int typelen;
	unsigned char wantreply;
	int ret = 1;
	struct ChanSess *chansess;

	TRACE(("enter chansessionrequest"))

	type = buf_getstring(ses.payload, &typelen);
	wantreply = buf_getbool(ses.payload);

	if (typelen > MAX_NAME_LEN) {
		TRACE(("leave chansessionrequest: type too long")) /* XXX send error?*/
		goto out;
	}

	chansess = (struct ChanSess*)channel->typedata;
	dropbear_assert(chansess != NULL);
	TRACE(("type is %s", type))

	if (strcmp(type, "window-change") == 0) {
		ret = sessionwinchange(chansess);
	} else if (strcmp(type, "shell") == 0) {
		ret = sessioncommand(channel, chansess, 0, 0);
	} else if (strcmp(type, "pty-req") == 0) {
		ret = sessionpty(chansess);
	} else if (strcmp(type, "exec") == 0) {
		ret = sessioncommand(channel, chansess, 1, 0);
	} else if (strcmp(type, "subsystem") == 0) {
		ret = sessioncommand(channel, chansess, 1, 1);
#if DROPBEAR_X11FWD
	} else if (strcmp(type, "x11-req") == 0) {
		ret = x11req(chansess);
#endif
#if DROPBEAR_SVR_AGENTFWD
	} else if (strcmp(type, "auth-agent-req@openssh.com") == 0) {
		ret = svr_agentreq(chansess);
#endif
	} else if (strcmp(type, "signal") == 0) {
		ret = sessionsignal(chansess);
	} else {
		/* etc, todo "env", "subsystem" */
	}

out:

	if (wantreply) {
		if (ret == DROPBEAR_SUCCESS) {
			send_msg_channel_success(channel);
		} else {
			send_msg_channel_failure(channel);
		}
	}

	m_free(type);
	TRACE(("leave chansessionrequest"))
}


/* Send a signal to a session's process as requested by the client*/
static int sessionsignal(const struct ChanSess *chansess) {
	TRACE(("sessionsignal"))

	int sig = 0;
	char* signame = NULL;
	int i;

	if (chansess->pid == 0) {
		TRACE(("sessionsignal: done no pid"))
		/* haven't got a process pid yet */
		return DROPBEAR_FAILURE;
	}

	if (svr_opts.forced_command || svr_pubkey_has_forced_command()) {
		TRACE(("disallowed signal for forced_command"));
		return DROPBEAR_FAILURE;
	}

	if (DROPBEAR_SVR_MULTIUSER && !DROPBEAR_SVR_DROP_PRIVS) {
		TRACE(("disallow signal without drop privs"));
		return DROPBEAR_FAILURE;
	}

	signame = buf_getstring(ses.payload, NULL);

	for (i = 0; signames[i].name != NULL; i++) {
		if (strcmp(signames[i].name, signame) == 0) {
			sig = signames[i].signal;
			break;
		}
	}

	m_free(signame);

	TRACE(("sessionsignal: pid %d signal %d", (int)chansess->pid, sig))
	if (sig == 0) {
		/* failed */
		return DROPBEAR_FAILURE;
	}
			
	if (kill(chansess->pid, sig) < 0) {
		TRACE(("sessionsignal: kill() errored"))
		return DROPBEAR_FAILURE;
	} 

	return DROPBEAR_SUCCESS;
}

/* Let the process know that the window size has changed, as notified from the
 * client. Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
static int sessionwinchange(const struct ChanSess *chansess) {

	int termc, termr, termw, termh;

	if (chansess->master < 0) {
		/* haven't got a pty yet */
		return DROPBEAR_FAILURE;
	}
			
	termc = buf_getint(ses.payload);
	termr = buf_getint(ses.payload);
	termw = buf_getint(ses.payload);
	termh = buf_getint(ses.payload);
	
	pty_change_window_size(chansess->master, termr, termc, termw, termh);

	return DROPBEAR_SUCCESS;
}

static void get_termmodes(const struct ChanSess *chansess) {

	struct termios termio;
	unsigned char opcode;
	unsigned int value;
	const struct TermCode * termcode;
	unsigned int len;

	TRACE(("enter get_termmodes"))

	/* Term modes */
	/* We'll ignore errors and continue if we can't set modes.
	 * We're ignoring baud rates since they seem evil */
	if (tcgetattr(chansess->master, &termio) == -1) {
		return;
	}

	len = buf_getint(ses.payload);
	TRACE(("term mode str %d p->l %d p->p %d", 
				len, ses.payload->len , ses.payload->pos));
	if (len != ses.payload->len - ses.payload->pos) {
		dropbear_exit("Bad term mode string");
	}

	if (len == 0) {
		TRACE(("leave get_termmodes: empty terminal modes string"))
		return;
	}

	while (((opcode = buf_getbyte(ses.payload)) != 0x00) && opcode <= 159) {

		/* must be before checking type, so that value is consumed even if
		 * we don't use it */
		value = buf_getint(ses.payload);

		/* handle types of code */
		if (opcode > MAX_TERMCODE) {
			continue;
		}
		termcode = &termcodes[(unsigned int)opcode];
		

		switch (termcode->type) {

			case TERMCODE_NONE:
				break;

			case TERMCODE_CONTROLCHAR:
				termio.c_cc[termcode->mapcode] = value;
				break;

			case TERMCODE_INPUT:
				if (value) {
					termio.c_iflag |= termcode->mapcode;
				} else {
					termio.c_iflag &= ~(termcode->mapcode);
				}
				break;

			case TERMCODE_OUTPUT:
				if (value) {
					termio.c_oflag |= termcode->mapcode;
				} else {
					termio.c_oflag &= ~(termcode->mapcode);
				}
				break;

			case TERMCODE_LOCAL:
				if (value) {
					termio.c_lflag |= termcode->mapcode;
				} else {
					termio.c_lflag &= ~(termcode->mapcode);
				}
				break;

			case TERMCODE_CONTROL:
				if (value) {
					termio.c_cflag |= termcode->mapcode;
				} else {
					termio.c_cflag &= ~(termcode->mapcode);
				}
				break;
				
		}
	}
	if (tcsetattr(chansess->master, TCSANOW, &termio) < 0) {
		dropbear_log(LOG_INFO, "Error setting terminal attributes");
	}
	TRACE(("leave get_termmodes"))
}

/* Set up a session pty which will be used to execute the shell or program.
 * The pty is allocated now, and kept for when the shell/program executes.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
static int sessionpty(struct ChanSess * chansess) {

	unsigned int termlen;
	char namebuf[65];
	struct passwd * pw = NULL;

	TRACE(("enter sessionpty"))

	if (!svr_pubkey_allows_pty()) {
		TRACE(("leave sessionpty : pty forbidden by public key option"))
		return DROPBEAR_FAILURE;
	}

	chansess->term = buf_getstring(ses.payload, &termlen);
	if (termlen > MAX_TERM_LEN) {
		/* TODO send disconnect ? */
		TRACE(("leave sessionpty: term len too long"))
		return DROPBEAR_FAILURE;
	}
#ifdef __ANDROID__
	/* Most Android user builds don't expose a usable devpts mount to app sandboxes. */
	dropbear_log(LOG_WARNING, "pty requested but unsupported; rejecting pty request");
	m_free(chansess->term);
	chansess->term = NULL;
	return DROPBEAR_FAILURE;
#endif
	/* allocate the pty */
	if (chansess->master != -1) {
		dropbear_exit("Multiple pty requests");
	}
	if (pty_allocate(&chansess->master, &chansess->slave, namebuf, 64) == 0) {
		TRACE(("leave sessionpty: failed to allocate pty"))
#ifdef __ANDROID__
		dropbear_log(LOG_WARNING, "pty_allocate failed, rejecting pty request");
		m_free(chansess->term);
		chansess->term = NULL;
		return DROPBEAR_FAILURE;
#else
		return DROPBEAR_FAILURE;
#endif
	}
	
	chansess->tty = m_strdup(namebuf);
	if (!chansess->tty) {
		dropbear_exit("Out of memory"); /* TODO disconnect */
	}

	pw = getpwnam(ses.authstate.pw_name);
	if (pw) {
		pty_setowner(pw, chansess->tty);
	} else {
		dropbear_log(LOG_WARNING, "getpwnam failed, skipping pty_setowner");
	}

	/* Set up the rows/col counts */
	sessionwinchange(chansess);

	/* Read the terminal modes */
	get_termmodes(chansess);

	TRACE(("leave sessionpty"))
	return DROPBEAR_SUCCESS;
}

#if !DROPBEAR_VFORK
static void make_connection_string(struct ChanSess *chansess) {
	char *local_ip, *local_port, *remote_ip, *remote_port;
	size_t len;
	get_socket_address(ses.sock_in, &local_ip, &local_port, &remote_ip, &remote_port, 0);

	/* "remoteip remoteport localip localport" */
	len = strlen(local_ip) + strlen(remote_ip) + 20;
	chansess->connection_string = m_malloc(len);
	snprintf(chansess->connection_string, len, "%s %s %s %s", remote_ip, remote_port, local_ip, local_port);

	/* deprecated but bash only loads .bashrc if SSH_CLIENT is set */ 
	/* "remoteip remoteport localport" */
	len = strlen(remote_ip) + 20;
	chansess->client_string = m_malloc(len);
	snprintf(chansess->client_string, len, "%s %s %s", remote_ip, remote_port, local_port);

	m_free(local_ip);
	m_free(local_port);
	m_free(remote_ip);
	m_free(remote_port);
}
#endif

/* Handle a command request from the client. This is used for both shell
 * and command-execution requests, and passes the command to
 * noptycommand or ptycommand as appropriate.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
static int sessioncommand(struct Channel *channel, struct ChanSess *chansess,
		int iscmd, int issubsys) {

	unsigned int cmdlen = 0;
	int ret;

	TRACE(("enter sessioncommand %d", channel->index))

	if (chansess->pid != 0) {
		/* Note that only one command can _succeed_. The client might try
		 * one command (which fails), then try another. Ie fallback
		 * from sftp to scp */
		TRACE(("leave sessioncommand, already have a command"))
		return DROPBEAR_FAILURE;
	}

	if (iscmd) {
		/* "exec" */
		if (chansess->cmd == NULL) {
			chansess->cmd = buf_getstring(ses.payload, &cmdlen);

			if (cmdlen > MAX_CMD_LEN) {
				m_free(chansess->cmd);
				/* TODO - send error - too long ? */
				TRACE(("leave sessioncommand, command too long %d", cmdlen))
				return DROPBEAR_FAILURE;
			}
		}
		if (issubsys) {
#if DROPBEAR_SFTPSERVER
			if ((cmdlen == 4) && strncmp(chansess->cmd, "sftp", 4) == 0) {
				char *expand_path = expand_homedir_path(SFTPSERVER_PATH);
				m_free(chansess->cmd);
				chansess->cmd = m_strdup(expand_path);
				m_free(expand_path);
			} else 
#endif
			{
				m_free(chansess->cmd);
				TRACE(("leave sessioncommand, unknown subsystem"))
				return DROPBEAR_FAILURE;
			}
		}
	}
	

	/* take global command into account */
	if (svr_opts.forced_command) {
		if (chansess->cmd) {
			chansess->original_command = chansess->cmd;
		} else {
			chansess->original_command = m_strdup("");
		}
		chansess->cmd = m_strdup(svr_opts.forced_command);
	} else {
		/* take public key option 'command' into account */
		svr_pubkey_set_forced_command(chansess);
	}


#if LOG_COMMANDS
	if (chansess->cmd) {
		dropbear_log(LOG_INFO, "User %s executing '%s'", 
						ses.authstate.pw_name, chansess->cmd);
	} else {
		dropbear_log(LOG_INFO, "User %s executing login shell", 
						ses.authstate.pw_name);
	}
#endif

	/* uClinux will vfork(), so there'll be a race as 
	connection_string is freed below. */
#if !DROPBEAR_VFORK
	make_connection_string(chansess);
#endif

	if (chansess->term == NULL) {
		/* no pty */
		ret = noptycommand(channel, chansess);
		if (ret == DROPBEAR_SUCCESS) {
			channel->prio = DROPBEAR_PRIO_NORMAL;
			update_channel_prio();
		}
	} else {
		/* want pty */
		ret = ptycommand(channel, chansess);
	}

#if !DROPBEAR_VFORK
	m_free(chansess->connection_string);
	m_free(chansess->client_string);
#endif

	if (ret == DROPBEAR_FAILURE) {
		m_free(chansess->cmd);
	}
	TRACE(("leave sessioncommand, ret %d", ret))
	return ret;
}

/* Execute a command and set up redirection of stdin/stdout/stderr without a
 * pty.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
static int noptycommand(struct Channel *channel, struct ChanSess *chansess) {
	int ret;

	TRACE(("enter noptycommand"))
	ret = spawn_command(execchild, chansess, 
			&channel->writefd, &channel->readfd, &channel->errfd,
			&chansess->pid);

	if (ret == DROPBEAR_FAILURE) {
		return ret;
	}

	ses.maxfd = MAX(ses.maxfd, channel->writefd);
	ses.maxfd = MAX(ses.maxfd, channel->readfd);
	ses.maxfd = MAX(ses.maxfd, channel->errfd);
	channel->bidir_fd = 0;

	addchildpid(chansess, chansess->pid);

	if (svr_ses.lastexit.exitpid != -1) {
		unsigned int i;
		TRACE(("parent side: lastexitpid is %d", svr_ses.lastexit.exitpid))
		/* The child probably exited and the signal handler triggered
		 * possibly before we got around to adding the childpid. So we fill
		 * out its data manually */
		for (i = 0; i < svr_ses.childpidsize; i++) {
			if (svr_ses.childpids[i].pid == svr_ses.lastexit.exitpid) {
				TRACE(("found match for lastexitpid"))
				svr_ses.childpids[i].chansess->exit = svr_ses.lastexit;
				svr_ses.lastexit.exitpid = -1;
				break;
			}
		}
	}

	TRACE(("leave noptycommand"))
	return DROPBEAR_SUCCESS;
}

/* Execute a command or shell within a pty environment, and set up
 * redirection as appropriate.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
static int ptycommand(struct Channel *channel, struct ChanSess *chansess) {

	pid_t pid;
	struct logininfo *li = NULL;
#if DO_MOTD
	buffer * motdbuf = NULL;
	int len;
	struct stat sb;
	char *hushpath = NULL;
#endif

	TRACE(("enter ptycommand"))

	/* we need to have a pty allocated */
	if (chansess->master == -1 || chansess->tty == NULL) {
		dropbear_log(LOG_WARNING, "No pty was allocated, couldn't execute");
		return DROPBEAR_FAILURE;
	}
	
#if DROPBEAR_VFORK
	pid = vfork();
#else
	pid = fork();
#endif
	if (pid < 0)
		return DROPBEAR_FAILURE;

	if (pid == 0) {
		/* child */
		
		TRACE(("back to normal sigchld"))
		/* Revert to normal sigchld handling */
		if (signal(SIGCHLD, SIG_DFL) == SIG_ERR) {
			dropbear_exit("signal() error");
		}
		
		/* redirect stdin/stdout/stderr */
		close(chansess->master);

		pty_make_controlling_tty(&chansess->slave, chansess->tty);
		
		if ((dup2(chansess->slave, STDIN_FILENO) < 0) ||
			(dup2(chansess->slave, STDOUT_FILENO) < 0)) {
			TRACE(("leave ptycommand: error redirecting filedesc"))
			return DROPBEAR_FAILURE;
			}

		/* write the utmp/wtmp login record - must be after changing the
		 * terminal used for stdout with the dup2 above, otherwise
		 * the wtmp login will not be recorded */
		li = chansess_login_alloc(chansess);

		svr_raise_gid_utmp();
		login_login(li);
		svr_restore_gid();

		login_free_entry(li);

		/* Can now dup2 stderr. Messages from login_login() have gone
		to the parent stderr */
		if (dup2(chansess->slave, STDERR_FILENO) < 0) {
			TRACE(("leave ptycommand: error redirecting filedesc"))
			return DROPBEAR_FAILURE;
		}

		close(chansess->slave);

#if DO_MOTD
		if (svr_opts.domotd && !chansess->cmd) {
			/* don't show the motd if ~/.hushlogin exists */

			/* 12 == strlen("/.hushlogin\0") */
			len = strlen(ses.authstate.pw_dir) + 12; 

			hushpath = m_malloc(len);
			snprintf(hushpath, len, "%s/.hushlogin", ses.authstate.pw_dir);

			if (stat(hushpath, &sb) < 0) {
				char *expand_path = NULL;
				/* more than a screenful is stupid IMHO */
				motdbuf = buf_new(MOTD_MAXSIZE);
				expand_path = expand_homedir_path(MOTD_FILENAME);
				if (buf_readfile(motdbuf, expand_path) == DROPBEAR_SUCCESS) {
					/* incase it is full size, add LF at last position */
					if (motdbuf->len == motdbuf->size) motdbuf->data[motdbuf->len - 1]=10;
					buf_setpos(motdbuf, 0);
					while (motdbuf->pos != motdbuf->len) {
						len = motdbuf->len - motdbuf->pos;
						len = write(STDOUT_FILENO, 
								buf_getptr(motdbuf, len), len);
						buf_incrpos(motdbuf, len);
					}
				}
				m_free(expand_path);
				buf_free(motdbuf);

			}
			m_free(hushpath);
		}
#endif /* DO_MOTD */

		execchild(chansess);
		/* not reached */

	} else {
		/* parent */
		TRACE(("continue ptycommand: parent"))
		chansess->pid = pid;

		/* add a child pid */
		addchildpid(chansess, pid);

		close(chansess->slave);
		channel->writefd = chansess->master;
		channel->readfd = chansess->master;
		/* don't need to set stderr here */
		ses.maxfd = MAX(ses.maxfd, chansess->master);
		channel->bidir_fd = 0;

		setnonblocking(chansess->master);

	}

	TRACE(("leave ptycommand"))
	return DROPBEAR_SUCCESS;
}

/* Add the pid of a child to the list for exit-handling */
static void addchildpid(struct ChanSess *chansess, pid_t pid) {

	unsigned int i;
	for (i = 0; i < svr_ses.childpidsize; i++) {
		if (svr_ses.childpids[i].pid == -1) {
			break;
		}
	}

	/* need to increase size */
	if (i == svr_ses.childpidsize) {
		svr_ses.childpids = (struct ChildPid*)m_realloc(svr_ses.childpids,
				sizeof(struct ChildPid) * (svr_ses.childpidsize+1));
		svr_ses.childpidsize++;
	}
	
	TRACE(("addchildpid %d pid %d for chansess %p", i, pid, chansess))
	svr_ses.childpids[i].pid = pid;
	svr_ses.childpids[i].chansess = chansess;

}

/* Clean up, drop to user privileges, set up the environment and execute
 * the command/shell. This function does not return. */
static void execchild(const void *user_data) {
	const struct ChanSess *chansess = user_data;
	char *usershell = NULL;
	char *cp = NULL;
	char *envcp = getenv("LANG");
	if (envcp != NULL) {
		cp = m_strdup(envcp);
	}

	/* with uClinux we'll have vfork()ed, so don't want to overwrite the
	 * hostkey. can't think of a workaround to clear it */
#if !DROPBEAR_VFORK
	/* wipe the hostkey */
	sign_key_free(svr_opts.hostkey);
	svr_opts.hostkey = NULL;

	/* overwrite the prng state */
	seedrandom();
#endif

	/* Save Methings environment vars BEFORE clearenv() wipes them.
	   These are set by SshdManager and need to reach child sessions. */
	char *saved_path = NULL;
	char *saved_env = NULL;
	char *saved_methings_home = NULL;
	char *saved_methings_pyenv = NULL;
	char *saved_methings_nativelib = NULL;
	char *saved_methings_bindir = NULL;
	char *saved_methings_wheelhouse = NULL;
	char *saved_ld_library_path = NULL;
	char *saved_pythonhome = NULL;
	char *saved_pythonpath = NULL;
	char *saved_ssl_cert_file = NULL;
	char *saved_pip_cert = NULL;
	char *saved_pip_find_links = NULL;
	char *saved_requests_ca_bundle = NULL;
	{
		const char *v;
		if ((v = getenv("PATH")) && v[0]) saved_path = m_strdup(v);
		if ((v = getenv("ENV")) && v[0]) saved_env = m_strdup(v);
		if ((v = getenv("METHINGS_HOME")) && v[0]) saved_methings_home = m_strdup(v);
		if ((v = getenv("METHINGS_PYENV")) && v[0]) saved_methings_pyenv = m_strdup(v);
		if ((v = getenv("METHINGS_NATIVELIB")) && v[0]) saved_methings_nativelib = m_strdup(v);
		if ((v = getenv("METHINGS_BINDIR")) && v[0]) saved_methings_bindir = m_strdup(v);
		if ((v = getenv("METHINGS_WHEELHOUSE")) && v[0]) saved_methings_wheelhouse = m_strdup(v);
		if ((v = getenv("LD_LIBRARY_PATH")) && v[0]) saved_ld_library_path = m_strdup(v);
		if ((v = getenv("PYTHONHOME")) && v[0]) saved_pythonhome = m_strdup(v);
		if ((v = getenv("PYTHONPATH")) && v[0]) saved_pythonpath = m_strdup(v);
		if ((v = getenv("SSL_CERT_FILE")) && v[0]) saved_ssl_cert_file = m_strdup(v);
		if ((v = getenv("PIP_CERT")) && v[0]) saved_pip_cert = m_strdup(v);
		if ((v = getenv("PIP_FIND_LINKS")) && v[0]) saved_pip_find_links = m_strdup(v);
		if ((v = getenv("REQUESTS_CA_BUNDLE")) && v[0]) saved_requests_ca_bundle = m_strdup(v);
	}

	/* clear environment if -e was not set */
	/* if we're debugging using valgrind etc, we need to keep the LD_PRELOAD
	 * etc. This is hazardous, so should only be used for debugging. */
	if ( !svr_opts.pass_on_env) {
#ifndef DEBUG_VALGRIND
#ifdef HAVE_CLEARENV
		clearenv();
#else /* don't HAVE_CLEARENV */
		/* Yay for posix. */
		if (environ) {
			environ[0] = NULL;
		}
#endif /* HAVE_CLEARENV */
#endif /* DEBUG_VALGRIND */
	}

#if !DROPBEAR_SVR_DROP_PRIVS
	svr_switch_user();
#endif

	/* set env vars */
	addnewvar("USER", ses.authstate.pw_name);
	addnewvar("LOGNAME", ses.authstate.pw_name);
	addnewvar("HOME", ses.authstate.pw_dir);
	addnewvar("SHELL", get_user_shell());
	if (saved_path) {
		addnewvar("PATH", saved_path);
	} else if (getuid() == 0) {
		addnewvar("PATH", DEFAULT_ROOT_PATH);
	} else {
		addnewvar("PATH", DEFAULT_PATH);
	}

	/* Restore Methings environment for child sessions. */
	if (saved_env) addnewvar("ENV", saved_env);
	if (saved_methings_home) addnewvar("METHINGS_HOME", saved_methings_home);
	if (saved_methings_pyenv) addnewvar("METHINGS_PYENV", saved_methings_pyenv);
	if (saved_methings_nativelib) addnewvar("METHINGS_NATIVELIB", saved_methings_nativelib);
	if (saved_methings_bindir) addnewvar("METHINGS_BINDIR", saved_methings_bindir);
	if (saved_methings_wheelhouse) addnewvar("METHINGS_WHEELHOUSE", saved_methings_wheelhouse);
	if (saved_ld_library_path) addnewvar("LD_LIBRARY_PATH", saved_ld_library_path);
	if (saved_pythonhome) addnewvar("PYTHONHOME", saved_pythonhome);
	if (saved_pythonpath) addnewvar("PYTHONPATH", saved_pythonpath);
	if (saved_ssl_cert_file) addnewvar("SSL_CERT_FILE", saved_ssl_cert_file);
	if (saved_pip_cert) addnewvar("PIP_CERT", saved_pip_cert);
	if (saved_pip_find_links) addnewvar("PIP_FIND_LINKS", saved_pip_find_links);
	if (saved_requests_ca_bundle) addnewvar("REQUESTS_CA_BUNDLE", saved_requests_ca_bundle);
	if (cp != NULL) {
		addnewvar("LANG", cp);
		m_free(cp);
	}	
	if (chansess->term != NULL) {
		addnewvar("TERM", chansess->term);
	}

	if (chansess->tty) {
		addnewvar("SSH_TTY", chansess->tty);
	}
	
	if (chansess->connection_string) {
		addnewvar("SSH_CONNECTION", chansess->connection_string);
	}

	if (chansess->client_string) {
		addnewvar("SSH_CLIENT", chansess->client_string);
	}
	
	if (chansess->original_command) {
		addnewvar("SSH_ORIGINAL_COMMAND", chansess->original_command);
	}
#if DROPBEAR_SVR_PUBKEY_OPTIONS_BUILT
	if (ses.authstate.pubkey_info != NULL) {
		addnewvar("SSH_PUBKEYINFO", ses.authstate.pubkey_info);
	}
#endif

	/* change directory */
	if (chdir(ses.authstate.pw_dir) < 0) {
		int e = errno;
		if (chdir("/") < 0) {
			dropbear_exit("chdir(\"/\") failed");
		}
		fprintf(stderr, "Failed chdir '%s': %s\n", ses.authstate.pw_dir, strerror(e));
	}


#if DROPBEAR_X11FWD
	/* set up X11 forwarding if enabled */
	x11setauth(chansess);
#endif
#if DROPBEAR_SVR_AGENTFWD
	/* set up agent env variable */
	svr_agentset(chansess);
#endif

#if defined(__ANDROID__)
	/* Build shell function preamble that maps commands to native lib binaries.
	   This avoids SELinux issues with symlinks/scripts in app_data_file. */
	char *methings_preamble = NULL;
	{
		const char *nlib = getenv("METHINGS_NATIVELIB");
		if (nlib && nlib[0]) {
				size_t plen = strlen(nlib) * 16 + 4096;
			methings_preamble = m_malloc(plen);
				snprintf(methings_preamble, plen,
					"python3(){ %s/libmethingspy.so \"$@\"; }; "
					"python(){ python3 \"$@\"; }; "
					/* Default to wheel-only installs on Android (no toolchains). Users can override by passing
					   --no-binary/--only-binary/--use-pep517/--no-use-pep517/--no-build-isolation explicitly. */
					"pip(){ "
						"if [ \"$1\" = \"install\" ]; then "
							"shift; "
							"_methings_add=1; "
							"for _a in \"$@\"; do "
								"case \"$_a\" in "
									"--only-binary*|--no-binary*|--prefer-binary|--no-build-isolation|--use-pep517|--no-use-pep517) _methings_add=0;; "
								"esac; "
							"done; "
							"if [ \"$_methings_add\" = \"1\" ]; then "
								"%s/libmethingspy.so -m pip install --only-binary=:all: --prefer-binary \"$@\"; "
							"else "
								"%s/libmethingspy.so -m pip install \"$@\"; "
							"fi; "
							"return $?; "
						"fi; "
						"%s/libmethingspy.so -m pip \"$@\"; "
					"}; "
					"pip3(){ pip \"$@\"; }; "
					/* Auto-bootstrap uv on first use if the module isn't installed yet. */
					"uv(){ %s/libmethingspy.so -c 'import importlib.util,sys;sys.exit(0 if importlib.util.find_spec(\"uv\") else 1)'; "
						"if [ $? -ne 0 ]; then %s/libmethingspy.so -m pip install uv || return $?; fi; "
						"%s/libmethingspy.so -m uv \"$@\"; }; "
					"uvx(){ uv tool run \"$@\"; }; "
					"curl(){ %s/libmethingspy.so -c 'import json,os,shlex,sys,urllib.request;"
						"u=\"http://127.0.0.1:8765/shell/exec\";"
						"d=json.dumps({\"cmd\":\"curl\",\"args\":shlex.join(sys.argv[1:]),\"cwd\":os.getcwd()}).encode();"
						"req=urllib.request.Request(u,data=d,headers={\"Content-Type\":\"application/json\"});"
						"r=urllib.request.urlopen(req,timeout=60);"
						"o=json.loads(r.read().decode(\"utf-8\",errors=\"replace\"));"
						"out=o.get(\"output\",\"\");"
						"sys.stdout.write(out if isinstance(out,str) else str(out));"
						"raise SystemExit(int(o.get(\"code\",1)))' \"$@\"; }; "
					/* Default ssh wrapper:
					   - Auto-accept unknown host keys (-y) unless the user already supplied -y.
					   - If the caller tries to open an interactive session but this shell doesn't
					     have a TTY, fail fast with a clear message (otherwise it looks "hung"). */
					"ssh(){ "
						"want_y=1; "
						"for a in \"$@\"; do "
							"case \"$a\" in "
								"-y) want_y=0;; "
							"esac; "
						"done; "
						"if [ \"$want_y\" = 1 ]; then set -- -y \"$@\"; fi; "
						"_m_has_cmd=0; _m_seen_host=0; _m_skip=0; _m_end_opts=0; "
						"for a in \"$@\"; do "
							"if [ \"$_m_skip\" = 1 ]; then _m_skip=0; continue; fi; "
								"if [ \"$_m_seen_host\" = 0 ]; then "
									"if [ \"$_m_end_opts\" = 1 ]; then _m_seen_host=1; _m_end_opts=0; continue; fi; "
									"case \"$a\" in "
										"--) _m_end_opts=1;; "
										"-p|-l|-i|-c|-m|-W|-K|-I|-o|-J|-b|-L|-R|-B|-s) _m_skip=1;; "
										"-*) ;; "
										"*) _m_seen_host=1;; "
									"esac; "
								"continue; "
							"fi; "
							"_m_has_cmd=1; break; "
						"done; "
						"if [ \"$_m_seen_host\" = 1 ] && [ \"$_m_has_cmd\" = 0 ] && ! test -t 0; then "
							"echo \"ssh: interactive sessions require a TTY. Use: ssh user@host <command>\" 1>&2; "
							"return 2; "
						"fi; "
						"%s/libdbclient.so \"$@\"; "
					"}; "
					"dbclient(){ ssh \"$@\"; }; "
					/* scp needs a program path for -S; use an executable in nativeLibraryDir. */
					"scp(){ "
						"have_s=0; want_v=0; "
						"if ! test -t 0; then want_v=1; fi; "
						"for a in \"$@\"; do "
							"case \"$a\" in "
								"-S) have_s=1;; "
								"-v) want_v=0;; "
								"-q) want_v=0;; "
							"esac; "
						"done; "
						"if [ \"$want_v\" = 1 ]; then set -- -v \"$@\"; fi; "
						"if [ \"$have_s\" = 1 ]; then "
							"%s/libscp.so \"$@\"; "
						"else "
							"%s/libscp.so -S %s/libmethingsdbclientwrap.so \"$@\"; "
						"fi; "
					"}; "
					/* put/get: scp alternative for environments where the scp protocol stalls (notably some
					   OpenSSH_for_Windows setups). Uses ssh + cat when available, otherwise PowerShell+base64. */
					"put(){ "
						"if [ $# -ne 2 ]; then echo \"usage: put <local_file> <user@host:remote_path_or_dir>\" 1>&2; return 2; fi; "
						"_l=\"$1\"; _r=\"$2\"; "
						"case \"$_r\" in *:*) :;; *) echo \"put: remote must be user@host:path\" 1>&2; return 2;; esac; "
						"_h=\"${_r%%:*}\"; _p=\"${_r#*:}\"; "
						"if [ -d \"$_l\" ]; then echo \"put: directories not supported\" 1>&2; return 2; fi; "
						"_bn=\"$(basename \"$_l\")\"; "
						"case \"$_p\" in */) _p=\"${_p}${_bn}\";; esac; "
						"ssh \"$_h\" \"command -v cat >/dev/null 2>&1\" >/dev/null 2>&1; "
						"if [ $? -eq 0 ]; then "
							/* Tilde expansion doesn't work inside quotes. Allow unquoted ~ paths. */
							"case \"$_p\" in ~*) ssh \"$_h\" \"cat > $_p\" < \"$_l\";; *) ssh \"$_h\" \"cat > \\\"$_p\\\"\" < \"$_l\";; esac; "
							"return $?; "
						"fi; "
						"command -v base64 >/dev/null 2>&1 || { echo \"put: base64 not found\" 1>&2; return 127; }; "
						"base64 \"$_l\" | ssh \"$_h\" "
							"\"powershell -NoProfile -Command \\\"$b64=[Console]::In.ReadToEnd() -replace '\\\\s','';"
							"$p='$_p'; if ($p.StartsWith('~/')) { $p=Join-Path $HOME $p.Substring(2) };"
							"[IO.File]::WriteAllBytes($p,[Convert]::FromBase64String($b64))\\\"\"; "
					"}; "
					"get(){ "
						"if [ $# -ne 2 ]; then echo \"usage: get <user@host:remote_file> <local_path>\" 1>&2; return 2; fi; "
						"_r=\"$1\"; _l=\"$2\"; "
						"case \"$_r\" in *:*) :;; *) echo \"get: remote must be user@host:path\" 1>&2; return 2;; esac; "
						"_h=\"${_r%%:*}\"; _p=\"${_r#*:}\"; "
						"ssh \"$_h\" \"command -v cat >/dev/null 2>&1\" >/dev/null 2>&1; "
						"if [ $? -eq 0 ]; then "
							"case \"$_p\" in ~*) ssh \"$_h\" \"cat $_p\" > \"$_l\";; *) ssh \"$_h\" \"cat \\\"$_p\\\"\" > \"$_l\";; esac; "
							"return $?; "
						"fi; "
						"command -v base64 >/dev/null 2>&1 || { echo \"get: base64 not found\" 1>&2; return 127; }; "
						"ssh \"$_h\" "
							"\"powershell -NoProfile -Command \\\"$b=[IO.File]::ReadAllBytes('$_p');"
							"[Convert]::ToBase64String($b)\\\"\" | base64 -d > \"$_l\"; "
					"}; "
					/* Node.js runtime (Termux-built) + npm/corepack assets (extracted by the app).
					   This is not Bun, but provides a Node-compatible shell environment when present. */
					"if [ -x \"${METHINGS_NATIVELIB}/libnode.so\" ]; then "
						"node(){ \"${METHINGS_NATIVELIB}/libnode.so\" \"$@\"; }; "
						"npm(){ "
							"_nr=\"${METHINGS_NODE_ROOT:-}\"; "
							"if [ -z \"$_nr\" ]; then _nr=\"${METHINGS_HOME%/user}/node\"; fi; "
							"NPM_CONFIG_PREFIX=\"${METHINGS_HOME}/npm-prefix\" "
							"NPM_CONFIG_CACHE=\"${METHINGS_HOME}/npm-cache\" "
							"\"${METHINGS_NATIVELIB}/libnode.so\" \"$_nr/usr/lib/node_modules/npm/bin/npm-cli.js\" \"$@\"; "
						"}; "
						"npx(){ "
							"_nr=\"${METHINGS_NODE_ROOT:-}\"; "
							"if [ -z \"$_nr\" ]; then _nr=\"${METHINGS_HOME%/user}/node\"; fi; "
							"NPM_CONFIG_PREFIX=\"${METHINGS_HOME}/npm-prefix\" "
							"NPM_CONFIG_CACHE=\"${METHINGS_HOME}/npm-cache\" "
							"\"${METHINGS_NATIVELIB}/libnode.so\" \"$_nr/usr/lib/node_modules/npm/bin/npx-cli.js\" \"$@\"; "
						"}; "
						"corepack(){ "
							"_nr=\"${METHINGS_NODE_ROOT:-}\"; "
							"if [ -z \"$_nr\" ]; then _nr=\"${METHINGS_HOME%/user}/node\"; fi; "
							"\"${METHINGS_NATIVELIB}/libnode.so\" \"$_nr/usr/lib/node_modules/corepack/dist/corepack.js\" \"$@\"; "
						"}; "
					"fi; "
						"dropbearkey(){ %s/libdropbearkey.so \"$@\"; }; ",
					nlib, nlib, nlib, nlib, nlib, nlib, nlib, nlib, nlib, nlib, nlib, nlib, nlib, nlib);
			}
		}

	if (chansess->cmd == NULL && chansess->term == NULL) {
		const char *prompt = "methings> ";
		char linebuf[1024];
		while (1) {
			size_t pos = 0;
			(void)write(1, prompt, strlen(prompt));
			while (1) {
				char ch;
				ssize_t r = read(0, &ch, 1);
				if (r <= 0) {
					_exit(0);
				}
				if (ch == '\r') {
					(void)write(1, "\r\n", 2);
					break;
				}
				if (ch == '\n') {
					(void)write(1, "\r\n", 2);
					break;
				}
				if (ch == '\b' || ch == 0x7f) {
					if (pos > 0) {
						pos--;
					}
					continue;
				}
				if (pos + 1 < sizeof(linebuf)) {
					linebuf[pos++] = ch;
				}
			}
			linebuf[pos] = '\0';
			if (pos == 0) {
				continue;
			}
			if (strcmp(linebuf, "exit") == 0 || strcmp(linebuf, "logout") == 0) {
				_exit(0);
			}
			if (strncmp(linebuf, "cd ", 3) == 0) {
				if (chdir(linebuf + 3) < 0) {
					dprintf(2, "cd: %s\n", strerror(errno));
				}
				continue;
			}
			pid_t pid = fork();
			if (pid == 0) {
				if (methings_preamble) {
					/* Prepend function defs so python3/pip resolve correctly */
					size_t wlen = strlen(methings_preamble) + strlen(linebuf) + 1;
					char *wrapped = m_malloc(wlen);
					snprintf(wrapped, wlen, "%s%s", methings_preamble, linebuf);
					execl("/system/bin/sh", "sh", "-c", wrapped, (char *)NULL);
				} else {
					execl("/system/bin/sh", "sh", "-c", linebuf, (char *)NULL);
				}
				_exit(127);
			} else if (pid > 0) {
				int status = 0;
				(void)waitpid(pid, &status, 0);
			} else {
				dprintf(2, "fork failed: %s\n", strerror(errno));
			}
		}
	}

	/* Wrap non-interactive commands with python3/pip function definitions */
	{
		const char *final_cmd = chansess->cmd;
		if (chansess->cmd != NULL && methings_preamble) {
			size_t wlen = strlen(methings_preamble) + strlen(chansess->cmd) + 1;
			char *wrapped = m_malloc(wlen);
			snprintf(wrapped, wlen, "%s%s", methings_preamble, chansess->cmd);
			final_cmd = wrapped;
		}
		usershell = m_strdup(get_user_shell());
		run_shell_command(final_cmd, ses.maxfd, usershell);
	}
#else
	usershell = m_strdup(get_user_shell());
	run_shell_command(chansess->cmd, ses.maxfd, usershell);
#endif

	/* only reached on error */
	dropbear_exit("Child failed");
}

/* Set up the general chansession environment, in particular child-exit
 * handling */
void svr_chansessinitialise() {

	struct sigaction sa_chld;

	/* single child process intially */
	svr_ses.childpids = (struct ChildPid*)m_malloc(sizeof(struct ChildPid));
	svr_ses.childpids[0].pid = -1; /* unused */
	svr_ses.childpids[0].chansess = NULL;
	svr_ses.childpidsize = 1;
	svr_ses.lastexit.exitpid = -1; /* Nothing has exited yet */
	sa_chld.sa_handler = sesssigchild_handler;
	sa_chld.sa_flags = SA_NOCLDSTOP;
	sigemptyset(&sa_chld.sa_mask);
	if (sigaction(SIGCHLD, &sa_chld, NULL) < 0) {
		dropbear_exit("signal() error");
	}
	
}

/* add a new environment variable, allocating space for the entry */
void addnewvar(const char* param, const char* var) {

	char* newvar = NULL;
	int plen, vlen;

	plen = strlen(param);
	vlen = strlen(var);

	newvar = m_malloc(plen + vlen + 2); /* 2 is for '=' and '\0' */
	memcpy(newvar, param, plen);
	newvar[plen] = '=';
	memcpy(&newvar[plen+1], var, vlen);
	newvar[plen+vlen+1] = '\0';
	/* newvar is leaked here, but that's part of putenv()'s semantics */
	if (putenv(newvar) < 0) {
		dropbear_exit("environ error");
	}
}
