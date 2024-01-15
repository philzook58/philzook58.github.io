
<https://ebpf.io/get-started/>
There's a doucmentary? what <https://www.youtube.com/watch?v=Wb_vD3XZYOA&ab_channel=SpeakeasyProductions>

<https://www.youtube.com/watch?v=J_EehoXLbIU&ab_channel=Computerphile> huh a computerphile. the hype machine is insane

Seccomp filters


ubpf
https://github.com/iovisor/ubpf
https://klyr.github.io/posts/playing_with_ubpf/

`ubpf_test` `ubpf_plugiin`
```bash
echo "
static int idouble(int a) {
    int temp = 0;
    while(a > 0){
        temp +=  a;
        a--;
        }
        return temp;
}

int bpf_prog(void *ctx) {
        int a = 3;
        a = idouble(a);

        return (a);
}
" > /tmp/hello.c
clang -O2 -target bpf -c /tmp/hello.c -o /tmp/hello.o
/home/philip/Downloads/ubpf/build/bin/ubpf_test /tmp/hello.o
```

https://www.brendangregg.com/blog/2019-01-01/learn-ebpf-tracing.html
```bash
#sudo opensnoop-bpfcc # see every open
#sudo execsnoop-bpfcc # see every exec
sudo bitesize-bpfcc #
sudo stackcount-bpfcc # see every stack trace. hmm.
```
execsnoop, opensnoop, ext4slower (or btrfs*, xfs*, zfs*), biolatency, biosnoop, cachestat, tcpconnect, tcpaccept, tcpretrans, runqlat, and profil

https://github.com/iovisor/bcc
bcc
```python
from bcc import BPF

BPF(text='int kprobe__sys_clone(void *ctx) { bpf_trace_printk("Hello, World!\\n"); return 0; }').trace_print()
```