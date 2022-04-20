#!/usr/bin/env python2
import os
import re
import shutil
import logging

from argparse import ArgumentParser
from tempfile import mkdtemp

import qsym

DEFAULT_TIMEOUT = 90

logger = logging.getLogger('qsym.concolic')

def parse_args():
    p = ArgumentParser()

    p.add_argument("-i", dest="input",   required=True, help="Input seed directory")
    p.add_argument("-o", dest="output",  required=True, help="QSYM output directory")
    p.add_argument("-p", dest="program", required=True, help="Path of the instrument program")
    p.add_argument("-r", dest="raw",     required=True, help="Path of the raw program")

    p.add_argument("cmd", nargs="+", help="cmdline, use %s to denote a file" % qsym.utils.AT_FILE)
    
    return p.parse_args()


def check_args(args):
    if not os.path.exists(args.input):
        raise ValueError('Invalid input path')
    
def mkdir(dirp):
    if not os.path.exists(dirp):
        os.makedirs(dirp)
    

def identify_id(seed):
    seed_pattern = re.compile(r'^id:(?P<id>\d+),.*$', re.DOTALL)
    matcher = seed_pattern.match(seed)
    if not matcher:
        return 'temp-id'
    id = matcher.groupdict()['id']
    return id


class ConcolicExecutor(object):
    def __init__(self, input, output, program, raw, cmd, afl_path='afl'):
        self.input   = input
        self.output  = output
        self.program = program
        self.raw = raw
        self.cmd = cmd

        self.bitmap     = os.path.join(self.output, "bitmap")
        self.queue_path = os.path.join(self.output, "queue")
        self.hangs_path = os.path.join(self.output, "hangs")
        self.error_path = os.path.join(self.output, "error")
        self.make_dirs()

        self.queue = list()
        self.minimizer = qsym.TestcaseMinimizer([program]+cmd, afl_path, self.output, False)
        self.filename = ".cur_input" 
        self.tmp_dir = mkdtemp()
        self.idx = 0
    
    @property
    def cur_input(self):
        return os.path.realpath(os.path.join(self.output, self.filename))

    @property
    def coverage(self):
        return len(filter(lambda x: x != 0, self.minimizer.bitmap))
    
    def make_dirs(self):
        mkdir(self.queue_path)
        mkdir(self.hangs_path)
        mkdir(self.error_path)    

    def perform_dry_run(self):
        # load initial seeds
        for fname in os.listdir(self.input):
            fpath = os.path.join(self.input, fname)
            if os.path.isfile(fpath):
                self.queue.append(fpath)
                self.minimizer.check_testcase(fpath)
        
        logger.debug("Initial seed num: %d" % len(self.queue))
        logger.debug("Initial edge coverage: %d" % self.coverage)

    
    def run_target(self):
        q = qsym.Executor([self.raw]+self.cmd, self.cur_input, self.tmp_dir, bitmap=self.bitmap, argv=["-l", "1"])
        ret = q.run(DEFAULT_TIMEOUT)
        logger.debug("Total=%d s, Emulation=%d s, Solver=%d s, Return=%d"
                     % (ret.total_time,
                        ret.emulation_time,
                        ret.solving_time,
                        ret.returncode))
        return q, ret
    

    def handle_ret(self, ret, fp):
        retcode = ret.returncode

        if retcode in [124, -9]:
            shutil.copy2(fp, os.path.join(self.hangs_path, os.path.basename(fp)))
        elif retcode in [128 + 11, -11, 128 + 6, -6]:
            # segfault or abort
            shutil.copy2(fp, os.path.join(self.error_path, os.path.basename(fp)))


    def clean_up(self):
        shutil.rmtree(self.tmp_dir)

    def run(self):
        self.perform_dry_run()
        queue_it = iter(self.queue)

        while True:
            try:
                fp = next(queue_it)
                shutil.copy2(fp, self.cur_input)
                logger.debug("Run qsym concolic: input=%s" % fp)

                q, ret = self.run_target()
                self.handle_ret(ret, fp)

                src_id = identify_id(os.path.basename(fp))

                testcase_cnt, interesting_cnt = 0, 0
                for testcase in q.get_testcases():
                    testcase_cnt += 1
                    if not self.minimizer.check_testcase(testcase):
                        os.unlink(testcase)
                        continue
                    
                    fpath = os.path.join(self.queue_path, "id:%06d,src:%s" % (self.idx, src_id))
                    shutil.move(testcase, fpath)
                    logger.debug("Creating: %s" % fpath)

                    interesting_cnt += 1
                    self.queue.append(fpath)
                    self.idx += 1
                
                logger.debug("Generate %d testcases" % testcase_cnt)
                logger.debug("%d testcases are interesting" % interesting_cnt)

                if os.path.exists(q.log_file):
                    os.unlink(q.log_file)

                try:
                    os.rmdir(q.testcase_directory)
                except Exception:
                    pass

            except StopIteration:
                logger.debug("No new seeds")
                break
            except KeyboardInterrupt:
                logger.debug('Have a nice day!')
                break

        self.clean_up()


def main():
    '''Running QSYM concolic all alone'''
    args = parse_args()
    check_args(args)

    e = ConcolicExecutor(args.input, args.output, args.program,
                         args.raw, args.cmd)
    e.run()


if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    main()