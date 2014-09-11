/* test_yuvcap.c
 *
 * History:
 *	2012/02/09 - [Jian Tang] created file
 *	2013/11/27 - [Zhaoyang Chen] modified file
 *
 * Copyright (C) 2007-2012, Ambarella, Inc.
 *
 * All rights reserved. No Part of this file may be reproduced, stored
 * in a retrieval system, or transmitted, in any form, or by any means,
 * electronic, mechanical, photocopying, recording, or otherwise,
 * without the prior consent of Ambarella, Inc.
 *
 */

#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <sched.h>
#include <pthread.h>

#include <sys/select.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/types.h>

#include <time.h>
#include <assert.h>

#include <basetypes.h>
#include "ambas_common.h"
#include "iav_drv.h"
#include "iav_drv_ex.h"
#include "ambas_vin.h"
#include "ambas_vout.h"
#include "amba_usb.h"
#include "datatx_lib.h"
#include <signal.h>

//ffmpeg
#include "libavcodec/avcodec.h"
#include "libavformat/avformat.h"
#include "libavdevice/avdevice.h"
#include "libswscale/swscale.h" 
#include <libavutil/imgutils.h>
#include <libavutil/opt.h>
#include <libavutil/pixfmt.h>
//zlog
#include "zlog.h"

AVFormatContext *fmtctx;
AVStream *video_st;
AVCodec *video_codec;
const int FPS = 30;/* 25 images/s */ 
const char *RDIP = "192.168.13.195";
unsigned int  RDPORT = 5678;
const unsigned int OUTWIDTH = 720;
const unsigned int OUTHEIGHT = 480;


//static AVCodec *codec;
//static AVCodecContext *codec_context = NULL;
//static AVFrame *frame;
static uint8_t endcode[] = {0, 0, 1, 0xb7};

static pthread_t enc_pid;
static pthread_mutex_t enc_mutex;
static pthread_cond_t enc_cond;

static FILE *f; 
static int rfifo, wfifo;
static int is_start_capture_YUV_data = 0;

typedef enum {
    GET_STREAM = 0,
    STOP_STREAM = 1,
}STREAM_STATUS;

typedef struct transfer_yuv_data_s 
{
    uint32_t count;
    STREAM_STATUS status;
    int64_t pts;
    //iav_yuv_buffer_info_ex_t info;
    AVFrame *pframe;
}transfer_yuv_data_t, *transfer_yuv_data_p;

#define MILLION (1000000)
#define TIMES (1000000)
#define BILLION (1000000000)

void dump_empty()
{
    return;
}
#if 0
#define TEST_FUNCTION_START_TIME() \
    struct timespec tpstart;\
    struct timespec tpend;\
    static signed long long timeif_func = 0;\
    do {\
        if(clock_gettime(CLOCK_MONOTONIC,&tpstart)){\
            zlog_error(DEBUG_LOG, "Fail to get start time for NULL, error: %d, %s", errno, strerror(errno));\
        }\
    }while(0)

#define TEST_FUNCTION_END_TIME() \
    do {\
        if(clock_gettime(CLOCK_MONOTONIC,&tpend)){\
            zlog_error(DEBUG_LOG, "Fail to get end time for NULL, errno:%d, %s", errno, strerror(errno));\
        }\
        \
        timeif_func += BILLION*(tpend.tv_sec - tpstart.tv_sec)+(tpend.tv_nsec-tpstart.tv_nsec);\
        zlog_info(DEBUG_LOG, "function time is %lld ms",(timeif_func)/TIMES);\
    }while(0)
    
#else

#define TEST_FUNCTION_START_TIME()   dump_empty()
#define TEST_FUNCTION_END_TIME()     dump_empty()

#endif

#ifndef VERIFY_BUFFERID
#define VERIFY_BUFFERID(x)	do {		\
			if ((x) < 0 || ((x) >= IAV_ENCODE_SOURCE_BUFFER_LAST)) {	\
				printf("Invalid buffer id %d.\n", (x));	\
				return -1;	\
			}	\
		} while (0)
#endif


typedef enum {
	CAPTURE_NONE = 255,
	CAPTURE_PREVIEW_BUFFER = 0,
	CAPTURE_MOTION_BUFFER,
	CAPTURE_RAW_BUFFER,
	CAPTURE_TYPE_NUM,
} CAPTURE_TYPE;

#define MAX_YUV_BUFFER_SIZE		(4096*3000)		// 4096x3000
#define MAX_ME1_BUFFER_SIZE		(MAX_YUV_BUFFER_SIZE / 16)	// 1/16 of 4096x3000
#define MAX_FRAME_NUM			(7300)

#define YUVCAP_PORT				(2024)

typedef enum {
	YUV420_IYUV = 0,	// Pattern: YYYYYYYYUUVV
	YUV420_YV12 = 1,	// Pattern: YYYYYYYYVVUU
	YUV420_NV12 = 2,	// Pattern: YYYYYYYYUVUV
} YUV_FORMAT;

int fd_iav;

static int transfer_method = TRANS_METHOD_NFS;
static int port = YUVCAP_PORT;

static int current_buffer = -1;
static int capture_select = 0;

static int yuv_buffer_id = 0;
static int yuv420_format = YUV420_IYUV;

static int me1_buffer_id = 0;
static int frame_count = 1;
static int quit_yuv_stream = 0;
static int print_time_stamp = 0;
static int verbose = 0;

const char *default_filename_nfs = "/mnt/media/test.yuv";
const char *default_filename_tcp = "media/test";
const char *default_host_ip_addr = "10.0.0.11";
const char *default_filename;
static char filename[256];
static int fd_yuv[IAV_ENCODE_SOURCE_TOTAL_NUM];
static int fd_me1[IAV_ENCODE_SOURCE_TOTAL_NUM];
static int fd_raw;

typedef struct zlog_info_s
{
    const char *config_filename;
    const char *normal_level;
    const char *debug_level;
    zlog_category_t *c_normal;
    zlog_category_t *c_debug;
}zlog_info_t;

zlog_info_t yuv_log = { \
        .config_filename = "/etc/zlog/conf/yuv.conf",
        .normal_level = "normal",
        .debug_level = "debug",
        .c_normal = NULL,
        .c_debug = NULL,
    };

#define DEBUG_LOG (yuv_log.c_debug)
#define NORMAL_LOG (yuv_log.c_normal)

static int init_zlog_config(zlog_info_t *log)
{
    if (NULL == log)
    {
        fprintf(stderr, "line:%d: %s() param error\n", __LINE__, __func__);
        return -1;
    }
    
    int32_t rc;

    rc = zlog_init(log->config_filename);
    if (rc)
    {
        fprintf(stderr, "line:%d, %s() called zlog_init function fail!\n", __LINE__, __func__);
        return -2;
    }

    log->c_normal = zlog_get_category(log->normal_level);
    if (NULL == log->c_normal) {
        fprintf(stderr, "LINE:%d, %s(), get category fail\n", __LINE__, __func__);
        zlog_fini();
        return -2;
    } 
    
    log->c_debug = zlog_get_category(log->debug_level);
    if (NULL == log->c_normal) {
        fprintf(stderr, "LINE:%d, %s(), get category fail\n", __LINE__, __func__);
        zlog_fini();
        return -2;
    }   
    
    zlog_info(log->c_normal, "zlog init finshion");
    return 0;
}

static int destroy_zlog_config(zlog_info_t *log)
{
    zlog_info(log->c_normal, "Destruction of the log configuration");
    zlog_fini();
    return 0;
}

typedef enum {
    READ_MODE = 0,
    WRITE_MODE = 1, 
}OPEN_FILE_MODE;

static int open_fifo_file(int *fd, OPEN_FILE_MODE mode)
{
    int ret = 0;
    zlog_debug(DEBUG_LOG, "function start!");
    if (NULL == fd)
    {
        zlog_error(NORMAL_LOG, "param error");
        ret = -1;
        goto fail;
    }

    zlog_info(NORMAL_LOG, "called mkfifo pre");
    int res = mkfifo("/tmp/my_fifo", 0777);  
    if (0 != res && 17 != errno)  
    {  
        zlog_error(NORMAL_LOG, "called mkfifo function: errno: %d, %s", errno, strerror(errno));
    } 
    zlog_info(NORMAL_LOG, "called mkfifo after");

    if (READ_MODE == mode)
    {
        if ((*fd = open("/tmp/my_fifo", O_RDWR, 0777)) < 0)
        {
            zlog_error(NORMAL_LOG, "called open function mode read: errno: %d, %s", errno, strerror(errno));
            ret = -1;
            goto fail;
        }

        
    }
    
    if (WRITE_MODE == mode)
    {
        if ((*fd = open("/tmp/my_fifo", O_RDWR, 0777)) < 0)
        {
            zlog_error(NORMAL_LOG, "called open function mode write: errno: %d, %s", errno, strerror(errno));
            ret = -1;
            goto fail;

        }
    }
    zlog_info(NORMAL_LOG, "open fifo file finish!");
    
fail:    
    return ret;
}

static int close_fifo_file(int *fd)
{
    if (NULL == fd)
    {
        zlog_error(NORMAL_LOG, "param error");
        return -1;
    }

    close(*fd);
    
    return 0;
}
static int convert_YUV_data_to_frame(iav_yuv_buffer_info_ex_t *info, AVFrame *frame)
{
    TEST_FUNCTION_START_TIME();

    int x, y;
	int width, height, pitch;
	u8* input = info->uv_addr;
	//static u32 time_stamp = 0, prev_stamp = 0, frame_count = 0;
	int ret = 0;
    zlog_debug(DEBUG_LOG, "function start");
    zlog_debug(DEBUG_LOG, "info->y_addr:%p, info->uv_addr:%p", info->y_addr, info->uv_addr);
#if 0
        AVFrame *pFrame,*pFrameYUV;  
        pFrame=avcodec_alloc_frame();
        
        pFrameYUV = frame;

        /*
        IAV_YUV_400_FORMAT = 0,
    	IAV_YUV_420_FORMAT = 1,
    	IAV_YUV_422_FORMAT = 2,
        */

        avpicture_fill((AVPicture *)pFrameYUV, NULL, AV_PIX_FMT_YUV420P, codec_context->width, codec_context->height);

        struct SwsContext *img_convert_ctx;
        enum AVPixelFormat srcFormat = AV_PIX_FMT_YUV420P;

        if (IAV_YUV_420_FORMAT == info->format) {
            srcFormat = AV_PIX_FMT_YUV420P;
        } else if (IAV_YUV_422_FORMAT == info->format) {
            srcFormat = AV_PIX_FMT_YUYV422;   ///< packed YUV 4:2:2, 16bpp, Y0 Cb Y1 Cr

        }

        get_yuv_data_frame(info, pFrame);
        
        
        img_convert_ctx = sws_getContext(info->width, info->height, srcFormat, codec_context->width, codec_context->height, AV_PIX_FMT_YUV420P, SWS_BICUBIC, NULL, NULL, NULL); 
        if (NULL == img_convert_ctx)
        {
            zlog_error(NORMAL_LOG, "sws_getContext() error");
        }
        if (0 == sws_scale(img_convert_ctx, (const uint8_t* const*)pFrame->data, pFrameYUV->linesize, 0, codec_context->height, pFrameYUV->data, pFrameYUV->linesize))
        {
            zlog_error(NORMAL_LOG, "sws_scale() error");
        }
        

#else


        //h.264 Y-frame
    	/* prepare  image */
    	/* Y  Cb Rb */
        zlog_debug(DEBUG_LOG, "info struct: width:%d, height:%d, pitch:%d\n", info->width, info->height, info->pitch);
#if 1
        zlog_debug(DEBUG_LOG, "frame->linesize[0]: %d", frame->linesize[0]);
    	for (y = 0; y < (info->height * info->width / info->pitch) ; y++) {
    		for (x = 0; x < info->width; x++) {
    			frame->data[0][y * frame->linesize[0] + x] = info->y_addr[y * frame->linesize[0] + x];
    		}
    	}
#else
        
        //zlog_debug(DEBUG_LOG, "info struct: width:%d, height:%d, pitch:%d\n", info->width, info->height, info->pitch);
    	for (y = 0; y < info->height; y++) {
            //zlog_debug(DEBUG_LOG, "y=%d", y);
    		//frame->data[0][y * frame->linesize[0] + x] = info->y_addr[y * frame->linesize[0] + x];
            memcpy(&frame->data[0][0] + y * frame->linesize[0], &info->y_addr[0] + y * frame->linesize[0], info->width);
    	}
#endif



        zlog_debug(DEBUG_LOG, "Convert Y Cb Rb");

        //U&V
    	// input yuv is uv interleaved with padding (uvuvuvuv.....)
    	if (IAV_YUV_420_FORMAT == info->format) {
    		width = info->width / 2;
    		height = info->height / 2;
    		pitch = info->pitch / 2;
    		if (yuv420_format == YUV420_YV12) {
    			// YV12 format (YYYYYYYYVVUU)
    			for (y = 0; y < height; ++y) {
    				input = info->uv_addr + y * pitch * 2;
    				for (x = 0; x < width; ++x) {
                        frame->data[1][y * frame->linesize[1] + x] = *input++;
                        frame->data[2][y * frame->linesize[2] + x] = *input++;
    				}
    			}
    		} else if (yuv420_format == YUV420_IYUV) {
    			// IYUV (I420) format (YYYYYYYYUUVV)
    			for (y = 0; y < height; ++y) {
    				input = info->uv_addr + y * pitch * 2;
    				for (x = 0; x < width; ++x) {
                        frame->data[1][y * frame->linesize[1] + x] = *input++;
                        frame->data[2][y * frame->linesize[2] + x] = *input++;
    				}
    			}
    		} else if (yuv420_format == YUV420_NV12) {//???
    			// NV12 format (YYYYYYYYUVUV)
    			for (y = 0; y < height; ++y) {
    				//memcpy(output + y * width * 2, info->uv_addr + y * pitch * 2, width * 2);
    			}
    		} else {
    			// YUV interleaved
    			zlog_error(NORMAL_LOG, "Unsupported YUV 420 output format!");
    			ret = -1;
    		}
            zlog_info(NORMAL_LOG, "IAV_YUV_420_FORMAT == info->format");
    	}
        else if (IAV_YUV_422_FORMAT == info->format) {
    		width = info->width / 2;
    		height = info->height;
    		pitch = info->pitch / 2;
    		// only YV16 format is supported
    		// YV16 format (YYYYYYYYUUUUVVVV)
    		for (y = 0; y < (info->height * info->width / info->pitch); ++y) {
    			input = info->uv_addr + y * pitch * 2;
    			for (x = 0; x < width; ++x) {
                    frame->data[1][y * frame->linesize[1] + x] = *input++;
                    frame->data[2][y * frame->linesize[2] + x] = *input++;
    			}
    		}
            zlog_info(NORMAL_LOG, "IAV_YUV_422_FORMAT == info->format");
    	} else {
    		zlog_error(NORMAL_LOG, "Error: Unsupported YUV input format!");
    		ret = -1;
    	}
        
#endif

    zlog_debug(NORMAL_LOG, "Convert U&V ok");

#if 0
    if (info->y_addr)
    {   
        zlog_debug(NORMAL_LOG, "free(info->y_addr)");
        free(info->y_addr);
        info->y_addr = NULL;
    }
    if (info->uv_addr)
    {
        zlog_debug(NORMAL_LOG, "free(info->uv_addr)");
        free(info->uv_addr);
        info->uv_addr = NULL;
    }
#endif    
    zlog_info(NORMAL_LOG, "YUV data process finish");

    TEST_FUNCTION_END_TIME();
    
    return ret;
}

static int write_YUV_data_to_queue(iav_yuv_buffer_info_ex_t *info, uint32_t status)
{
    int ret = 0;
    static int64_t pts = 0;    
    transfer_yuv_data_t *p_write_buff = NULL;
    
    TEST_FUNCTION_START_TIME();

    static int frame_num = 1;
    zlog_debug(DEBUG_LOG, "function start!");
    
    if (NULL == info && 0 == status)
    {
        zlog_error(NORMAL_LOG, "param error");
        ret = -1;
        goto _fail;
    }
    

    transfer_yuv_data_t write_buff;
    p_write_buff = &write_buff;
    memset(p_write_buff, 0, sizeof(transfer_yuv_data_t));

    if (NULL != info)
    {
        zlog_debug(DEBUG_LOG, "NULL != info");
#if 0        
        iav_yuv_buffer_info_ex_t *p_info = &p_write_buff->info;
        memcpy(p_info, info, sizeof(iav_yuv_buffer_info_ex_t));
       
        p_info->y_addr = (u8 *)malloc((p_info->height * p_info->width) * sizeof(u8));
        p_info->uv_addr = (u8 *)malloc((p_info->height * p_info->width) * sizeof(u8));
        memset(p_info->y_addr, 0, (p_info->height * p_info->width) * sizeof(u8));
        memset(p_info->uv_addr, 0, (p_info->height * p_info->width) * sizeof(u8));
        memcpy(p_info->y_addr, info->y_addr, p_info->height * p_info->width);
        memcpy(p_info->uv_addr, info->uv_addr, p_info->height * p_info->width);
#else
        AVFrame *avframe = av_frame_alloc();

        avframe->format = video_st->codec->pix_fmt;
        avframe->width = video_st->codec->width;
        avframe->height = video_st->codec->height;

        zlog_info(NORMAL_LOG, "video_st->codec->pix_fmt:%d, video_st->codec->width:%d, video_st->codec->height: %d", video_st->codec->pix_fmt, video_st->codec->width, video_st->codec->height);
        ret = av_image_alloc(avframe->data, avframe->linesize, video_st->codec->width, video_st->codec->height, video_st->codec->pix_fmt, 32);
        if (ret < 0) {
            zlog_error(NORMAL_LOG, "Could not allocate raw picture buffer");
            return -1;
        }
        convert_YUV_data_to_frame(info, avframe);
        p_write_buff->pframe = avframe;
#endif
        zlog_debug(DEBUG_LOG, "NULL != info End");

    }
    p_write_buff->count = frame_num;
    p_write_buff->pts = pts;
    (pts == ~((int64_t)1 << 63))? (pts = 0): ++pts;

    p_write_buff->status = status;
    
    int32_t *fd = &wfifo;
    int32_t maxfd = *fd + 1;
    fd_set fdset;
    FD_ZERO(&fdset);
    FD_SET(*fd, &fdset);

    int data_num = 0;
#if 1    
    zlog_debug(DEBUG_LOG, "select pre");
    select(maxfd, NULL, &fdset, NULL, NULL);
    if(FD_ISSET(*fd, &fdset))
#endif 
    {
        zlog_debug(DEBUG_LOG, "write pre");
        if ((data_num = write(*fd, p_write_buff, sizeof(transfer_yuv_data_t))) < 0 )
        {
            zlog_error(NORMAL_LOG, "called write function error:%d, %s", errno, strerror(errno));
            ret = -2;
            goto _fail;
        }
    }
    FD_CLR(*fd, &fdset);

    zlog_debug(DEBUG_LOG, "function end!, write (frame:%d) to data size: %d byte!", ++frame_num, data_num);

_fail:
    TEST_FUNCTION_END_TIME();
    return ret;
}

//encoder thread
int got_output = 0;
   
static int encodec_YUV_data_to_h264(AVFrame *frame)
{
    TEST_FUNCTION_START_TIME();

    zlog_debug(DEBUG_LOG, "function start");
#if 0
    int got_output = 0;
    int ret = 0;
    AVPacket pkt;

    av_init_packet(&pkt);
    pkt.data = NULL; // packet data will be allocated by the encoder
    pkt.size = 0;

    /* encode the image */
    ret = avcodec_encode_video2(codec_context, &pkt, frame, &got_output);
    if (ret < 0) {
        zlog_error(NORMAL_LOG, "Error encoding frame");
    	return -1;
    }

    if (got_output) {
        zlog_info(NORMAL_LOG, "Write frame (size=%5d)", pkt.size);
        //write(pipe_fd[1], pkt.data, pkt.size);
        fwrite(pkt.data, 1, pkt.size, f);
    	av_free_packet(&pkt);
    }
#else
    /* encode the image */
    int ret;
    AVPacket pkt;
    av_init_packet(&pkt);
    pkt.stream_index  = video_st->index;

#if 1  
    pkt.data = NULL;    // packet data will be allocated by the encoder
    pkt.size = 0;
#else
    pkt.data = (uint8_t *)frame;
    pkt.size = sizeof(AVPicture);
    pkt.pts = AV_NOPTS_VALUE;
    pkt.dts =AV_NOPTS_VALUE;
#endif

    //frame->pts = video_st->codec->frame_number;
    ret = avcodec_encode_video2(video_st->codec, &pkt, frame, &got_output);
    if (ret < 0) {
        fprintf(stderr, "Error encoding video frame: %s\n", av_err2str(ret));
        exit(1);
    }
    
        
    /* If size is zero, it means the image was buffered. */
    if (got_output) 
    {
        if (video_st->codec->coded_frame->key_frame)pkt.flags |= AV_PKT_FLAG_KEY;
            pkt.stream_index = video_st->index;
        if (pkt.pts != AV_NOPTS_VALUE )
        {
            pkt.pts = av_rescale_q(pkt.pts,video_st->codec->time_base, video_st->time_base);
        }
        if(pkt.dts !=AV_NOPTS_VALUE )
        {
            pkt.dts = av_rescale_q(pkt.dts,video_st->codec->time_base, video_st->time_base);
        }
        
        zlog_debug(NORMAL_LOG, "pkt.data: %p, pkt.size: %d", pkt.data, pkt.size);
        //fwrite(pkt.data, 1, pkt.size, f);
        /* Write the compressed frame to the media file. */
        ret = av_interleaved_write_frame(fmtctx, &pkt);
        av_free_packet(&pkt);
    } 
    else 
    {
        ret = 0;
    }
#endif
    
    TEST_FUNCTION_END_TIME();
    return 0;
}

#if 0
static int get_yuv_data_frame(iav_yuv_buffer_info_ex_t *info, AVFrame *frame)
{
	int width, height, pitch;
	u8* input = info->uv_addr;
	u8* output_u;
	u8* output_v;
	int i, j;
	static u32 time_stamp = 0, prev_stamp = 0;
	int ret = 0;
    
	// input yuv is uv interleaved with padding (uvuvuvuv.....)
	if (info->format == IAV_YUV_420_FORMAT) {
		width = info->width / 2;
		height = info->height / 2;
		pitch = info->pitch / 2;
		if (yuv420_format == YUV420_YV12) {
			// YV12 format (YYYYYYYYVVUU)
			//output_u = output + width * height;
			//output_v = output;
			for (i = 0; i < height; ++i) {
				input = info->uv_addr + i * pitch * 2;
				for (j = 0; j < width; ++j) {
                    frame->data[1] = *input++;
                    frame->data[2] = *input++;
                    //*output_u++ = *input++;
					//*output_v++ = *input++;
				}
			}
		} else if (yuv420_format == YUV420_IYUV) {
			// IYUV (I420) format (YYYYYYYYUUVV)
			//output_u = output;
			//output_v = output + width * height;
			for (i = 0; i < height; ++i) {
				input = info->uv_addr + i * pitch * 2;
				for (j = 0; j < width; ++j) {
                    frame->data[1] = *input++;
                    frame->data[2] = *input++;
					//*output_u++ = *input++;
					//*output_v++ = *input++;
				}
			}
		} else if (yuv420_format == YUV420_NV12) {
			// NV12 format (YYYYYYYYUVUV)
			for (i = 0; i < height; ++i) {
				//memcpy(output + i * width * 2, info->uv_addr + i * pitch * 2, width * 2);
			}
		} else {
			// YUV interleaved
			zlog_error(NORMAL_LOG, "Unsupported YUV 420 output format!");
			ret = -1;
		}
	} else if (info->format == IAV_YUV_422_FORMAT) {
		width = info->width / 2;
		height = info->height;
		pitch = info->pitch / 2;
		// only YV16 format is supported
		// YV16 format (YYYYYYYYUUUUVVVV)
		//output_u = output;
		//output_v = output + width * height;
		for (i = 0; i < height; ++i) {
			input = info->uv_addr + i * pitch * 2;
			for (j = 0; j < width; ++j) {
                frame->data[1] = *input++;
                frame->data[2] = *input++;
				//*output_u++ = *input++;
				//*output_v++ = *input++;
			}
		}
	} else {
		zlog_error(NORMAL_LOG, "Error: Unsupported YUV input format!");
		ret = -1;
	}
}
#endif



static int read_YUV_data_from_queue(transfer_yuv_data_t *readBuff)
{
    TEST_FUNCTION_START_TIME();

    static int frame_num = 1;
    zlog_debug(DEBUG_LOG, "function start!");
    int ret = 0;
    if (NULL == readBuff)
    {
        zlog_error(DEBUG_LOG, "param error");
        ret = -1;
        goto _fail;
    }
    
    int num = 0;

    int *fd = &rfifo;
    int maxfd = *fd + 1;
    fd_set fdset;
    FD_ZERO(&fdset);
    FD_SET(*fd, &fdset);
#if 1    
    zlog_debug(DEBUG_LOG, "select pre");
    select(maxfd, &fdset, NULL, NULL, NULL);
    if(FD_ISSET(*fd, &fdset))
#endif 
    {
        zlog_debug(DEBUG_LOG, "read pre");
        zlog_debug(DEBUG_LOG, "---ENC---; reading frame:%d from the fifo file", frame_num);
        if ((num = read(*fd, readBuff, sizeof(transfer_yuv_data_t))) < 0 )
        {
            zlog_error(NORMAL_LOG, "called read function: errno: %d, %s", errno, strerror(errno));
            ret = -2;
            goto _fail;
        }
    }
    FD_CLR(*fd, &fdset);
    
    zlog_debug(DEBUG_LOG, "function end, read (frame: %d)to data size: %d byte!", frame_num, num);

_fail:
    
    TEST_FUNCTION_END_TIME();
    zlog_debug(DEBUG_LOG, "---ENC---; read frame:%d from the fifo file, OK", readBuff->count);
    ++frame_num;
    return ret;
}


#if 0
static int read_YUV_data_from_avi()
{
     return 0;
}
#endif

static int destroy_encoder_pthread()
{
    zlog_debug(DEBUG_LOG, "function start!");
    pthread_join(enc_pid, NULL);
    pthread_mutex_destroy(&enc_mutex);
    pthread_cond_destroy(&enc_cond);
    zlog_info(NORMAL_LOG, "encoder pthread destory!");
    return 0;
}

//encoder main

static void * encoder_main(void *arg)
{
    
    zlog_info(NORMAL_LOG, "encoder pthread start!");
    
    TEST_FUNCTION_START_TIME();
    transfer_yuv_data_t yuvbuff;
    zlog_info(NORMAL_LOG,"called open_fifo_file pre!");
    open_fifo_file(&rfifo, READ_MODE);
    zlog_info(NORMAL_LOG, "called open_fifo_file OK!");
    
    pthread_mutex_lock(&enc_mutex);
    while (0 == is_start_capture_YUV_data)
    {
        pthread_cond_wait(&enc_cond, &enc_mutex);
    }
    pthread_mutex_unlock(&enc_mutex);
    zlog_debug(NORMAL_LOG, "while pre");
    while (1)
    {
        memset(&yuvbuff, 0, sizeof(transfer_yuv_data_t));
        //read a frame YUV data
        read_YUV_data_from_queue(&yuvbuff);
        
        //is stop encodec
        zlog_debug(DEBUG_LOG, "read stream EOF flag status: %s", (STOP_STREAM == yuvbuff.status? "YES":"NO"));
        if (STOP_STREAM == yuvbuff.status)
        {
            zlog_info(NORMAL_LOG, "receive EOF flag, stop encodec!");
            break;
        }
        
        //frame->pts = yuvbuff.pts;
        
        //convert YUV data;
        //convert_YUV_data_to_frame(&yuvbuff.info, frame);
        
        //encodec YUV data to H.264
        encodec_YUV_data_to_h264(yuvbuff.pframe);
        av_freep(&yuvbuff.pframe->data[0]);
        av_frame_free(&yuvbuff.pframe);
        
        zlog_debug(DEBUG_LOG, "---ENC---; encodec frame:%d, OK", yuvbuff.count);
    }
    
    while (got_output)
    {
        encodec_YUV_data_to_h264(NULL);
//        av_freep(&yuvbuff.pframe->data[0]);
//        av_frame_free(&yuvbuff.pframe);
    }
    close_fifo_file(&rfifo);
    //fwrite(endcode, 1, sizeof(endcode), f);
    
    TEST_FUNCTION_END_TIME();
    zlog_info(NORMAL_LOG, "encoder pthread exit!");
    return NULL;
}

static int create_encoder_pthread(pthread_t *pid)
{
    zlog_debug(DEBUG_LOG, "function start!");

    pthread_mutex_init(&enc_mutex, NULL);
    pthread_cond_init(&enc_cond, NULL);
    pthread_attr_t thread_attr;
    //int thread_policy;
    //struct sched_param thread_param;
    //int status, rr_min_priority, rr_max_priority;
    
    pthread_attr_init(&thread_attr);
    
#if 0    
//#if defined(_POSIX_THREAD_PRIORITY_SCHEDULING)
    pthread_attr_getschedpolicy(&thread_attr, &thread_policy);
    pthread_attr_getschedparam(&thread_attr, &thread_param);
    printf("Default policy is %s, priority is %d\n",
        (thread_policy == SCHED_FIFO ? "FIFO"
         : (thread_policy == SCHED_RR ? "RR"
            : (thread_policy == SCHED_OTHER ? "OTHER"
               : "unknown"))),
        thread_param.sched_priority);

    status = pthread_attr_setschedpolicy(&thread_attr, SCHED_RR);
    if(status != 0)
        printf("Unable to set SCHED_RR policy.\n");
    else{
        rr_min_priority = sched_get_priority_min(SCHED_RR);
        if(rr_min_priority == -1)
            printf("Get SCHED_RR min priority");
        rr_max_priority = sched_get_priority_max(SCHED_RR);
        if(rr_max_priority == -1)
            printf("Get SCHED_RR max priority");
        //thread_param.sched_priority = (rr_min_priority + rr_max_priority)/2;
        thread_param.sched_priority = 99;
        printf("SCHED_RR priority range is %d to %d: using %d\n",
            rr_min_priority, rr_max_priority, thread_param.sched_priority);
        pthread_attr_setschedparam(&thread_attr, &thread_param);
        printf("Creating thread at RR/%d\n", thread_param.sched_priority);
        pthread_attr_setinheritsched(&thread_attr, PTHREAD_EXPLICIT_SCHED);
    }
    
    if(pthread_create(pid, &thread_attr, encoder_main, NULL) != 0)
    {
        zlog_error(NORMAL_LOG, "called pthread_create function error: %d, %s", errno, strerror(errno));
        return -1;
    }

#else
    if(pthread_create(pid, NULL, encoder_main, NULL) != 0)
    {
        zlog_error(NORMAL_LOG, "called pthread_create function error: %d, %s", errno, strerror(errno));
        return -1;
    }
#endif    
    zlog_info(NORMAL_LOG, "Create encoder pthread complete!");
    return 0;
}

static int map_buffer(void)
{
	static int mem_mapped = 0;
	iav_mmap_info_t info;

	if (mem_mapped)
		return 0;

	if (ioctl(fd_iav, IAV_IOC_MAP_DSP, &info) < 0) {
        zlog_error(NORMAL_LOG, "IAV_IOC_MAP_DSP, errno: %d, %s", errno, strerror(errno));
		return -1;
	}

	mem_mapped = 1;
	return 0;
}

#if 0
static int save_yuv_luma_buffer(u8* output, iav_yuv_buffer_info_ex_t * info)
{
	int i;
	u8 *in;
	u8 *out;

	if (info->pitch < info->width) {
		printf("pitch size smaller than width!\n");
		return -1;
	}

    printf("info->pitch:%d; info->width:%d; info->height:%d\n", info->pitch, info->width, info->height);
	if (info->pitch == info->width) {
        printf("[LINE:%d]%s()\n", __LINE__, __func__);
		memcpy(output, info->y_addr, info->width * info->height);
	} else {
		in = info->y_addr;
		out = output;
		for (i = 0; i < info->height; i++) {		//row
			memcpy(out, in, info->width);
			in += info->pitch;
			out += info->width;
		}
	}

//h.264 Y-frame
	/* prepare  image */
	/* Y  Cb Rb */
	for (y = 0; y < codec_context->height; y++) {
		for (x = 0; x < codec_context->width; x++) {
            //printf("frame->linesize[0]= %d\n", frame->linesize[0]);
			//frame->data[0][y * frame->linesize[0] + x] = luma[y	* frame->linesize[0] * 2 + 2 * x];
			frame->data[0][y * frame->linesize[0] + x] = info->y_addr[y * frame->linesize[0] + x];
		}
	}

    

	return 0;
}

static int save_yuv_chroma_buffer(u8* output, iav_yuv_buffer_info_ex_t * info)
{
	int width, height, pitch;
	u8* input = info->uv_addr;
	u8* output_u;
	u8* output_v;
	int i, j;
	static u32 time_stamp = 0, prev_stamp = 0, frame_count = 0;
	int ret = 0;

	// input yuv is uv interleaved with padding (uvuvuvuv.....)
	if (info->format == IAV_YUV_420_FORMAT) {
		width = info->width / 2;
		height = info->height / 2;
		pitch = info->pitch / 2;
		if (yuv420_format == YUV420_YV12) {
			// YV12 format (YYYYYYYYVVUU)
			output_u = output + width * height;
			output_v = output;
			for (i = 0; i < height; ++i) {
				input = info->uv_addr + i * pitch * 2;
				for (j = 0; j < width; ++j) {
                    frame->data[1][i * frame->linesize[1] + j] = *input;
                    *output_u++ = *input++;
                    frame->data[2][i * frame->linesize[2] + j] = *input;
                    *output_v++ = *input++;
				}
			}
		} else if (yuv420_format == YUV420_IYUV) {
			// IYUV (I420) format (YYYYYYYYUUVV)
			output_u = output;
			output_v = output + width * height;
			for (i = 0; i < height; ++i) {
				input = info->uv_addr + i * pitch * 2;
				for (j = 0; j < width; ++j) {
                    frame->data[1][i * frame->linesize[1] + j] = *input;
                    *output_u++ = *input++;
                    frame->data[2][i * frame->linesize[2] + j] = *input;
                    *output_v++ = *input++;
				}
			}
		} else if (yuv420_format == YUV420_NV12) {
			// NV12 format (YYYYYYYYUVUV)
			for (i = 0; i < height; ++i) {
				memcpy(output + i * width * 2, info->uv_addr + i * pitch * 2, width * 2);
			}
		} else {
			// YUV interleaved
			printf("Error: Unsupported YUV 420 output format!\n");
			ret = -1;
		}
	} else if (info->format == IAV_YUV_422_FORMAT) {
		width = info->width / 2;
		height = info->height;
		pitch = info->pitch / 2;
		// only YV16 format is supported
		// YV16 format (YYYYYYYYUUUUVVVV)
		output_u = output;
		output_v = output + width * height;
		for (i = 0; i < height; ++i) {
			input = info->uv_addr + i * pitch * 2;
			for (j = 0; j < width; ++j) {
                frame->data[1][i * frame->linesize[1] + j] = *input;
                *output_u++ = *input++;
                frame->data[2][i * frame->linesize[2] + j] = *input;
                *output_v++ = *input++;
			}
		}
	} else {
		printf("Error: Unsupported YUV input format!\n");
		ret = -1;
	}
#if 0
    	/* Cb and Cr */
	for (y = 0; y < codec_context->height; y++) {
		for (x = 0; x < codec_context->width / 2; x++) {
			//frame->data[0][y * frame->linesize[0] + 2*x  ] = yuyv[y*frame->linesize[0]*4+4*x];
			//frame->data[0][y * frame->linesize[0] + 2*x+1] = yuyv[y*frame->linesize[0]*4+4*x+2];
		#if 0
			frame->data[1][y * frame->linesize[1] + x] = chroma[y * frame->linesize[1] * 4 + 4 * x + 1];
			frame->data[2][y * frame->linesize[2] + x] = chroma[y * frame->linesize[2] * 4 + 4 * x + 3];
        #endif

		}
	}
#endif

	if (ret == 0) {
		if (print_time_stamp) {
			input = info->uv_addr + pitch * height * 2;
			time_stamp = ((input[3] << 24) | (input[2] << 16) |
				(input[1] << 8) | (input[0]));
			printf("=[%2d]============== time stamp : [0x%08X], prev [0x%08X], diff [%u].\n",
				frame_count, time_stamp, prev_stamp, (time_stamp - prev_stamp));
			prev_stamp = time_stamp;
			++frame_count;
		}
	}

	return ret;
}

static int save_yuv_data(int fd, int buffer, iav_yuv_buffer_info_ex_t * info,
	u8 * luma, u8 * chroma)
{
	static int pts_prev = 0, pts = 0;
	int luma_size, chroma_size;

	luma_size = info->width * info->height;
	if (info->format == IAV_YUV_420_FORMAT) {
		chroma_size = luma_size / 2;
	} else if (info->format == IAV_YUV_422_FORMAT) {
		chroma_size = luma_size;
	} else {
		printf("Error: Unrecognized yuv data format from DSP!\n");
		return -1;
	}

    printf("info->format:%s\n", info->format == IAV_YUV_420_FORMAT ? "IAV_YUV_420_FORMAT" : info->format == IAV_YUV_422_FORMAT ? "IAV_YUV_422_FORMAT": "Don't know");

//luma
    if (save_yuv_luma_buffer(luma, info) < 0) {
		perror("Failed to save luma data into buffer !\n");
		return -1;
	}
    
	if (amba_transfer_write(fd, luma, luma_size, transfer_method) < 0) {
		perror("Failed to save luma data into file !\n");
	 	return -1;
	}
   

//chroma   
	if (save_yuv_chroma_buffer(chroma, info) < 0) {
		perror("Failed to save chroma data into buffer !\n");
		return -1;
	}

	if (amba_transfer_write(fd, chroma,	chroma_size, transfer_method) < 0) {
		perror("Failed to save chroma data into file !\n");
	 	return -1;
	}
    

	if (verbose) {
		pts = info->PTS;
		printf("BUF [%d] Y 0x%08x, UV 0x%08x, pitch %u, %ux%u = Seqnum[%u], PTS [%u-%u].\n",
			buffer, (u32)info->y_addr, (u32)info->uv_addr, info->pitch,
			info->width, info->height, info->seqnum, pts, (pts - pts_prev));
		pts_prev = pts;
	}

	return 0;
}

/*
**
**Called: capture_yuv(yuv_buffer_id, frame_count);
*/
static int capture_yuv(int buff_id, int count)
{
	int i, buf, save[IAV_ENCODE_SOURCE_TOTAL_NUM];
	char yuv_file[256];
	u8 * luma = NULL;
	u8 * chroma = NULL;
	char format[32];
	iav_yuv_buffer_info_ex_t info;
	iav_source_buffer_format_ex_t buf_format;
    int got_output;

	luma = malloc(MAX_YUV_BUFFER_SIZE);
	if (luma == NULL) {
		printf("Not enough memory for preview capture !\n");
		goto yuv_error_exit;
	}
	chroma = malloc(MAX_YUV_BUFFER_SIZE);
	if (chroma == NULL) {
		printf("Not enough memory for preivew capture !\n");
		goto yuv_error_exit;
	}
	memset(save, 0, sizeof(save));
#if 1
    while(1 != quit_yuv_stream) {
#else
	for (i = 0; i < count; ++i) {
#endif
		for (buf = IAV_ENCODE_SOURCE_BUFFER_FIRST;
			buf < IAV_ENCODE_SOURCE_BUFFER_LAST; ++buf) {
			if (buff_id & (1 << buf)) {
                
                av_init_packet(&pkt);
                pkt.data = NULL; // packet data will be allocated by the encoder
                pkt.size = 0;
             
				if (fd_yuv[buf] < 0) {
					memset(&buf_format, 0, sizeof(buf_format));
					buf_format.source = buf;
					if (ioctl(fd_iav, IAV_IOC_GET_SOURCE_BUFFER_FORMAT_EX, &buf_format) < 0) {
						perror("IAV_IOC_GET_SOURCE_BUFFER_FORMAT_EX");
						continue;
					}
                    
					memset(yuv_file, 0, sizeof(yuv_file));
					sprintf(yuv_file, "%s_prev_%c_%dx%d.yuv", filename,
						(current_buffer == IAV_ENCODE_SOURCE_MAIN_BUFFER) ? 'M' :
						('a' + IAV_ENCODE_SOURCE_FOURTH_BUFFER - current_buffer),
						buf_format.size.width, buf_format.size.height);
					fd_yuv[buf] = amba_transfer_open(yuv_file,
						transfer_method, port++);
					if (fd_yuv[buf] < 0) {
						printf("Cannot open file [%s].\n", yuv_file);
						continue;
					}
				}
                
				info.source = buf;
				if (ioctl(fd_iav, IAV_IOC_READ_YUV_BUFFER_INFO_EX, &info) < 0) {
					if (errno == EINTR) {
						continue;		/* back to for() */
					} else {
						perror("IAV_IOC_READ_YUV_BUFFER_INFO_EX");
						goto yuv_error_exit;
					}
				}
				if ((info.y_addr == NULL) || (info.uv_addr == NULL)) {
					printf("YUV buffer [%d] address is NULL! Skip to next!\n", buf);
					continue;
				}
				if (save_yuv_data(fd_yuv[buf], buf, &info, luma, chroma) < 0) {
					printf("Failed to save YUV data of buf [%d].\n", buf);
					goto yuv_error_exit;
				}
				if (save[buf] == 0) {
					save[buf] = 1;
					if (info.format == IAV_YUV_422_FORMAT) {
						sprintf(format, "YV16");
					} else if (info.format == IAV_YUV_420_FORMAT) {
						switch (yuv420_format) {
						case YUV420_YV12:
							sprintf(format, "YV12");
							break;
						case YUV420_NV12:
							sprintf(format, "NV12");
							break;
						case YUV420_IYUV:
							sprintf(format, "IYUV");
							break;
						default:
							sprintf(format, "IYUV");
							break;
						}
					} else {
						sprintf(format, "Unknown [%d]", info.format);
					}
					printf("Capture_yuv_buffer : resolution %dx%d in %s format\n",
						info.width, info.height, format);
				}
#if 1                
                frame->pts = i;

	time_t timep;
	timep = time(NULL);
	printf("frame encodec pre:%s\n", asctime(gmtime(&timep)));

                /* encode the image */
                ret = avcodec_encode_video2(codec_context, &pkt, frame, &got_output);
                if (ret < 0) {
                	fprintf(stderr, "Error encoding frame\n");
                	exit(1);
                }

                if (got_output) {
                	printf("Write frame %3d (size=%5d)\n", i, pkt.size);
                	fwrite(pkt.data, 1, pkt.size, f);
                	av_free_packet(&pkt);
                }
	timep = time(NULL);
	printf("frame encodec OK:%s\n", asctime(gmtime(&timep)));
#endif        
    		}
		}
	}

	free(luma);
	free(chroma);
	return 0;

yuv_error_exit:
	if (luma)
		free(luma);
	if (chroma)
		free(chroma);
	return -1;
}
#else

#if 1
static int capture_yuv(int buff_id, int count)
{
    zlog_debug(DEBUG_LOG, "function start!");
    TEST_FUNCTION_START_TIME();
    
    int i = -1;
	int buf;
//	char yuv_file[256];
//	char format[32];
	iav_yuv_buffer_info_ex_t info;
    
#if 0
    int save[IAV_ENCODE_SOURCE_TOTAL_NUM];
    u8 * luma = NULL;
	u8 * chroma = NULL;
	iav_source_buffer_format_ex_t buf_format;

	luma = malloc(MAX_YUV_BUFFER_SIZE);
	if (luma == NULL) {
        zlog_error(NORMAL_LOG, "Not enough memory for preview capture !");
		goto yuv_error_exit;
	}
	chroma = malloc(MAX_YUV_BUFFER_SIZE);
	if (chroma == NULL) {
        zlog_error(NORMAL_LOG, "Not enough memory for preivew capture !");
		goto yuv_error_exit;
	}
	memset(save, 0, sizeof(save));
#endif

    is_start_capture_YUV_data= 1;
    //pthread_mutex_lock(&enc_mutex);
    
    zlog_debug(DEBUG_LOG, "pthread_cond_signal pre");
    pthread_cond_signal(&enc_cond);
    zlog_debug(DEBUG_LOG, "pthread_cond_signal after");
    
    //pthread_mutex_unlock(&enc_mutex);

#if 1
    while(1) {
        if (1 == quit_yuv_stream)
        {
            write_YUV_data_to_queue(NULL, 1);
            zlog_warn(NORMAL_LOG, "Stop to caputer YUV data!");
            break;
        }
#else
	for (i = 0; i < count; ++i) {
#endif
		for (buf = IAV_ENCODE_SOURCE_BUFFER_FIRST;
			buf < IAV_ENCODE_SOURCE_BUFFER_LAST; ++buf) {
			if (buff_id & (1 << buf)) {
#if 0                
                if(clock_gettime(CLOCK_MONOTONIC,&tpstart))
                {
                    zlog_error(DEBUG_LOG, "Fail to get start time for NULL, error: %d, %s", errno, strerror(errno));
                    return -1;
                }
#endif                    
				info.source = buf;
                zlog_debug(DEBUG_LOG, "---YUV---; Capturing frame:%d YUV data; buf: %d", i + 1, buf);
				if (ioctl(fd_iav, IAV_IOC_READ_YUV_BUFFER_INFO_EX, &info) < 0) {
					if (errno == EINTR) {
						continue;/* back to for() */
					} else {
					    zlog_error(NORMAL_LOG, "IAV_IOC_READ_YUV_BUFFER_INFO_EX, errno: %d, %s", errno, strerror(errno));
						goto yuv_error_exit;
					}
				}
                zlog_debug(DEBUG_LOG, "---YUV---; Capture frame:%d YUV data, OK", i + 1);
				if ((info.y_addr == NULL) || (info.uv_addr == NULL)) {
					zlog_error(NORMAL_LOG, "YUV buffer [%d] address is NULL! Skip to next!", buf);
					continue;
				}
#if 0                
                if(clock_gettime(CLOCK_MONOTONIC, &tpend))
                {
                    zlog_error(DEBUG_LOG, "Fail to get end time for NULL, errno:%d, %s", errno, strerror(errno));
                    return -1;
                }
                
                timeif_func += BILLION*(tpend.tv_sec - tpstart.tv_sec)+(tpend.tv_nsec-tpstart.tv_nsec);
                zlog_info(DEBUG_LOG, "function time is %lld ms",(timeif_func)/TIMES);
#endif
                
                zlog_debug(DEBUG_LOG, "---YUV---; Writing frame: %d to the fifo file", i+1);
                write_YUV_data_to_queue(&info, 0);                
                zlog_debug(DEBUG_LOG, "---YUV---; Write frame: %d to the fifo file, OK", i+1);

    		}
		}
	}

    write_YUV_data_to_queue(NULL, 1);
    zlog_info(NORMAL_LOG, "stop to capture YUV data!");
    zlog_debug(DEBUG_LOG, "function end!");

    TEST_FUNCTION_END_TIME();
	return 0;

yuv_error_exit:
    zlog_debug(DEBUG_LOG, "function end!");
	return -1;
}
#else
/*
**
**Called: capture_yuv(yuv_buffer_id, frame_count);
*/
static int capture_yuv(int buff_id, int count)
{
    TEST_FUNCTION_START_TIME();
  
    zlog_debug(DEBUG_LOG, "function start!");
    
    int i = -1;
	int buf, save[IAV_ENCODE_SOURCE_TOTAL_NUM];
	char yuv_file[256];
	char format[32];
	iav_yuv_buffer_info_ex_t info;
    
    u8 * luma = NULL;
	u8 * chroma = NULL;

	iav_source_buffer_format_ex_t buf_format;

	luma = malloc(MAX_YUV_BUFFER_SIZE);
	if (luma == NULL) {
        zlog_error(NORMAL_LOG, "Not enough memory for preview capture !");
		goto yuv_error_exit;
	}
	chroma = malloc(MAX_YUV_BUFFER_SIZE);
	if (chroma == NULL) {
        zlog_error(NORMAL_LOG, "Not enough memory for preivew capture !");
		goto yuv_error_exit;
	}
	memset(save, 0, sizeof(save));

    is_start_capture_YUV_data= 1;
    //pthread_mutex_lock(&enc_mutex);
    
    zlog_debug(DEBUG_LOG, "pthread_cond_signal pre");
    pthread_cond_signal(&enc_cond);
    zlog_debug(DEBUG_LOG, "pthread_cond_signal after");
    
    //pthread_mutex_unlock(&enc_mutex);
    
#if 0
    while(1) {
        if (1 == quit_yuv_stream)
        {
            write_YUV_data_to_queue(NULL, 1);
            printf("[%s:%d] Stop to caputer YUV data!\n", __func__, __LINE__);
            break;
        }
#else
	for (i = 0; i < count; ++i) {
#endif
		for (buf = IAV_ENCODE_SOURCE_BUFFER_FIRST;
			buf < IAV_ENCODE_SOURCE_BUFFER_LAST; ++buf) {
			if (buff_id & (1 << buf)) {
#if 0                
				if (fd_yuv[buf] < 0) {
					memset(&buf_format, 0, sizeof(buf_format));
					buf_format.source = buf;
					if (ioctl(fd_iav, IAV_IOC_GET_SOURCE_BUFFER_FORMAT_EX, &buf_format) < 0) {
                        zlog_error(NORMAL_LOG, "IAV_IOC_GET_SOURCE_BUFFER_FORMAT_EX, errno: %d, %s", errno, strerror(errno));
						continue;
					}
                    
					memset(yuv_file, 0, sizeof(yuv_file));
					sprintf(yuv_file, "%s_prev_%c_%dx%d.yuv", filename,
						(current_buffer == IAV_ENCODE_SOURCE_MAIN_BUFFER) ? 'M' :
						('a' + IAV_ENCODE_SOURCE_FOURTH_BUFFER - current_buffer),
						buf_format.size.width, buf_format.size.height);
					fd_yuv[buf] = amba_transfer_open(yuv_file,
						transfer_method, port++);
					if (fd_yuv[buf] < 0) {
                        zlog_error(NORMAL_LOG, "Cannot open file [%s].", yuv_file);
						continue;
					}
				}
                
#endif          
                
                if(clock_gettime(CLOCK_MONOTONIC,&tpstart))
                {
                    zlog_error(DEBUG_LOG, "Fail to get start time for NULL, error: %d, %s", errno, strerror(errno));
                    return -1;
                }
                    
				info.source = buf;
                zlog_debug(DEBUG_LOG, "---YUV---; Capturing frame:%d YUV data", i + 1);
				if (ioctl(fd_iav, IAV_IOC_READ_YUV_BUFFER_INFO_EX, &info) < 0) {
					if (errno == EINTR) {
						continue;/* back to for() */
					} else {
					    zlog_error(NORMAL_LOG, "IAV_IOC_READ_YUV_BUFFER_INFO_EX, errno: %d, %s", errno, strerror(errno));
						goto yuv_error_exit;
					}
				}
                zlog_debug(DEBUG_LOG, "---YUV---; Capture frame:%d YUV data, OK", i + 1);
				if ((info.y_addr == NULL) || (info.uv_addr == NULL)) {
					zlog_error(NORMAL_LOG, "YUV buffer [%d] address is NULL! Skip to next!", buf);
					continue;
				}
                
                if(clock_gettime(CLOCK_MONOTONIC, &tpend))
                {
                    zlog_error(DEBUG_LOG, "Fail to get end time for NULL, errno:%d, %s", errno, strerror(errno));
                    return -1;
                }
                timeif_func += BILLION*(tpend.tv_sec - tpstart.tv_sec)+(tpend.tv_nsec-tpstart.tv_nsec);
                zlog_info(DEBUG_LOG, "function time is %lld ms",(timeif_func)/TIMES);
#if 0
                
				if (save_yuv_data(fd_yuv[buf], buf, &info, luma, chroma) < 0) {
					printf("Failed to save YUV data of buf [%d].\n", buf);
					goto yuv_error_exit;
				}
#endif     
                zlog_debug(DEBUG_LOG, "---YUV---; Writing frame: %d to the fifo file", i+1);
                write_YUV_data_to_queue(&info, 0);                
                zlog_debug(DEBUG_LOG, "---YUV---; Write frame: %d to the fifo file, OK", i+1);
    		}
		}
	}
    

    write_YUV_data_to_queue(NULL, 1);
    zlog_info(NORMAL_LOG, "stop to capture YUV data!");
    
	free(luma);
	free(chroma);
    zlog_debug(DEBUG_LOG, "function end!");

    TEST_FUNCTION_END_TIME();
	return 0;

yuv_error_exit:
	if (luma)
		free(luma);
	if (chroma)
		free(chroma);
    
    zlog_debug(DEBUG_LOG, "function end!");
	return -1;
}
#endif
#endif
static int save_me1_luma_buffer(u8* output, iav_me1_buffer_info_ex_t * info)
{
	int i;
	u8 *in;
	u8 *out;

	if (info->pitch < info->width) {
		zlog_error(NORMAL_LOG, "pitch size smaller than width!\n");
		return -1;
	}

	if (info->pitch == info->width) {
		memcpy(output, info->addr, info->width * info->height);
	} else {
		in = info->addr;
		out = output;
		for (i = 0; i < info->height; i++) {		//row
			memcpy(out, in, info->width);
			in += info->pitch;
			out += info->width;
		}
	}

	return 0;
}


static int save_me1_data(int fd, int buffer, iav_me1_buffer_info_ex_t * info,
	u8 * y_buf, u8 * uv_buf)
{
	static u32 pts_prev = 0, pts = 0;

	save_me1_luma_buffer(y_buf,info);

	if (amba_transfer_write(fd, y_buf,
		info->width * info->height, transfer_method) < 0) {
		perror("Failed to save ME1 data into file !\n");
		return -1;
	}

	if (amba_transfer_write(fd, uv_buf,
		info->width * info->height / 2, transfer_method) < 0) {
		perror("Failed to save ME1 data into file !\n");
		return -1;
	}

	if (verbose) {
		pts = info->PTS;
		printf("BUF [%d] 0x%08x, pitch %d, %dx%d, seqnum [%d], PTS [%d-%d].\n",
			buffer, (u32)info->addr, info->pitch, info->width,
			info->height, info->seqnum, pts, (pts - pts_prev));
		pts_prev = pts;
	}

	return 0;
}

static int capture_me1(int buff_id, int count)
{
	int i, buf, save[IAV_ENCODE_SOURCE_TOTAL_NUM];
	char me1_file[256];
	u8 * luma = NULL;
	u8 * chroma = NULL;
	iav_me1_buffer_info_ex_t info;
	iav_source_buffer_format_ex_t buf_format;

	luma = malloc(MAX_ME1_BUFFER_SIZE);
	if (luma == NULL) {
		printf("Not enough memory for ME1 buffer capture !\n");
		goto me1_error_exit;
	}

	//clear UV to be B/W mode, UV data is not useful for motion detection,
	//just fill UV data to make YUV to be YV12 format, so that it can play in YUV player
	chroma = malloc(MAX_ME1_BUFFER_SIZE);
	if (chroma == NULL) {
		printf("Not enough memory for ME1 buffer capture !\n");
		goto me1_error_exit;
	}
	memset(chroma, 0x80, MAX_ME1_BUFFER_SIZE);
	memset(save, 0, sizeof(save));

	for (i = 0; i < count; ++i) {
		for (buf = IAV_ENCODE_SOURCE_BUFFER_FIRST;
			buf < IAV_ENCODE_SOURCE_BUFFER_LAST; ++buf) {
			if (buff_id & (1 << buf)) {
				if (fd_me1[buf] < 0) {
					memset(&buf_format, 0, sizeof(buf_format));
					buf_format.source = buf;
					if (ioctl(fd_iav, IAV_IOC_GET_SOURCE_BUFFER_FORMAT_EX, &buf_format) < 0) {
						perror("IAV_IOC_GET_SOURCE_BUFFER_FORMAT_EX");
						continue;
					}
					memset(me1_file, 0, sizeof(me1_file));
					sprintf(me1_file, "%s_me1_%c_%dx%d.yuv", filename,
						(buf == IAV_ENCODE_SOURCE_MAIN_BUFFER) ? 'm' :
						('a' + IAV_ENCODE_SOURCE_FOURTH_BUFFER - current_buffer),
						buf_format.size.width >> 2, buf_format.size.height >> 2);
					fd_me1[buf] = amba_transfer_open(me1_file,
						transfer_method, port++);
					if (fd_me1[buf] < 0) {
						printf("Cannot open file [%s].\n", me1_file);
						continue;
					}
				}
				info.source = buf;
				if (ioctl(fd_iav, IAV_IOC_READ_ME1_BUFFER_INFO_EX, &info) < 0) {
					if (errno == EINTR) {
						continue;		/* back to for() */
					} else {
						perror("IAV_IOC_READ_ME1_BUFFER_INFO_EX");
						goto me1_error_exit;
					}
				}
				if (info.addr == NULL) {
					printf("ME1 buffer [%d] address is NULL! Skip to next!\n", buf);
					continue;
				}
				if (save_me1_data(fd_me1[buf], buf, &info, luma, chroma) < 0) {
					printf("Failed to save ME1 data of buf [%d].\n", buf);
					goto me1_error_exit;
				}
				if (save[buf] == 0) {
					save[buf] = 1;
					printf("Save_me1_buffer : resolution %dx%d in YV12 format\n",
						info.width, info.height);
				}
			}
		}
	}

	free(luma);
	free(chroma);
	return 0;

me1_error_exit:
	if (luma)
		free(luma);
	if (chroma)
		free(chroma);
	return -1;
}

static int capture_raw(void)
{
	iav_raw_info_t info;
	u8 * raw_buffer = NULL;
	struct amba_video_info vin_info;
	iav_system_resource_setup_ex_t resource;
	u32 vin_width, vin_height, buffer_size;
	char raw_file[256];

	memset(&vin_info, 0, sizeof(vin_info));
	if (ioctl(fd_iav, IAV_IOC_VIN_SRC_GET_VIDEO_INFO, &vin_info) < 0) {
		perror("IAV_IOC_VIN_SRC_GET_VIDEO_INFO");
		return -1;
	}
	vin_width = vin_info.width;
	vin_height = vin_info.height;
	buffer_size = vin_width * vin_height * 2;
	raw_buffer = (u8 *)malloc(buffer_size);
	if (raw_buffer == NULL) {
		printf("Not enough memory for read out raw buffer!\n");
		return -1;
	}
	memset(raw_buffer, 0, buffer_size);

	memset(raw_file, 0, sizeof(raw_file));
	sprintf(raw_file, "%s_raw.raw", filename);
	fd_raw = amba_transfer_open(raw_file,
		transfer_method, port++);
	if (fd_raw < 0) {
		printf("Cannot open file [%s].\n", raw_file);
		goto raw_error_exit;
	}
	memset(&info, 0, sizeof(info));
	if (ioctl(fd_iav, IAV_IOC_READ_RAW_INFO, &info) < 0) {
		if (errno == EINTR) {
			// skip to do nothing
		} else {
			perror("IAV_IOC_READ_RAW_INFO");
			goto raw_error_exit;
		}
	}

	memset(&resource, 0, sizeof(resource));
	if (ioctl(fd_iav, IAV_IOC_GET_SYSTEM_RESOURCE_LIMIT_EX, &resource) < 0) {
		perror("IAV_IOC_GET_SYSTEM_RESOURCE_LIMIT_EX");
		goto raw_error_exit;
	}
	if (resource.raw_capture_enable &&
		((info.width != vin_width) || (info.height != vin_height))) {
		printf("VIN resolution %dx%d, raw data info %dx%d is incorrect!\n",
			vin_width, vin_height, info.width, info.height);
		goto raw_error_exit;
	}
	memcpy(raw_buffer, info.raw_addr, buffer_size);
	if (amba_transfer_write(fd_raw, raw_buffer, buffer_size,
		transfer_method) < 0) {
		perror("Failed to save RAW data into file !\n");
		goto raw_error_exit;
	}

	amba_transfer_close(fd_raw, transfer_method);
	free(raw_buffer);
	printf("save raw buffer done!\n");
	printf("VIN resolution %d x %d, Raw data %d x %d.\n",
		vin_width, vin_height, info.width, info.height);

	return 0;

raw_error_exit:
	if (raw_buffer)
		free(raw_buffer);
	if (fd_raw >= 0) {
		amba_transfer_close(fd_raw, transfer_method);
		fd_raw = -1;
	}
	return -1;
}

#define NO_ARG		0
#define HAS_ARG		1

struct hint_s {
	const char *arg;
	const char *str;
};

static const char *short_options = "b:f:F:mpr:RtuvY";

static struct option long_options[] = {
	{"buffer",		HAS_ARG, 0, 'b'},
	{"yuv",		NO_ARG, 0, 'Y'},
	{"me1",		NO_ARG, 0, 'm'},		/*capture me1 buffer */
	{"raw",		NO_ARG, 0, 'R'},
	{"filename",	HAS_ARG, 0, 'f'},		/* specify file name*/
	{"format",	HAS_ARG, 0, 'F'},
	{"tcp", 		NO_ARG, 0, 't'},
	{"usb",		NO_ARG, 0,'u'},
	{"frames",	HAS_ARG,0, 'r'},
	{"print-time-stamp",	NO_ARG, 0, 'p'},
	{"verbose",	NO_ARG, 0, 'v'},

	{0, 0, 0, 0}
};

static const struct hint_s hint[] = {
	{"0~3", "select source buffer id, 0 for main, 1 for 2nd buffer, 2 for 3rd buffer, 3 for 4th buffer"},
	{"",	"\tcapture YUV data from source buffer"},
	{"",	"\tcapture me1 data from source buffer"},
	{"",	"\tcapture raw data"},
	{"?.yuv",	"filename to store output yuv"},
	{"0|1",	"YUV420 data format for encode buffer, 0: IYUV(I420), 1: YV12, 2: NV12. Default is IYUV format"},
	{"",	"\tuse tcp to send data to PC"},
	{"",	"\tuse usb to send data to PC"},
	{"1~n",	"frame counts to capture"},
	{"",	"print time stamp for preview A YUV buffer data"},
	{"",	"\tprint more messages"},
};

static void usage(void)
{
	u32 i;
	for (i = 0; i < sizeof(long_options) / sizeof(long_options[0]) - 1; i++) {
		if (isalpha(long_options[i].val))
			printf("-%c ", long_options[i].val);
		else
			printf("   ");
		printf("--%s", long_options[i].name);
		if (hint[i].arg[0] != 0)
			printf(" [%s]", hint[i].arg);
		printf("\t%s\n", hint[i].str);
	}
	printf("\n\nThis program captures YUV or ME1 buffer in YUV420 format for encode buffer, and save as IYUV, YV12 or NV12.\n");
	printf("  IYUV format (U and V are planar buffers) is like :\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tUUUUUUUUUUUUUU\n"
		 "\t\tUUUUUUUUUUUUUU\n"
		 "\t\tVVVVVVVVVVVVVV\n"
		 "\t\tVVVVVVVVVVVVVV\n");
	printf("  YV12 format (U and V are planar buffers) is like :\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tVVVVVVVVVVVVVV\n"
		 "\t\tVVVVVVVVVVVVVV\n"
		 "\t\tUUUUUUUUUUUUUU\n"
		 "\t\tUUUUUUUUUUUUUU\n");
	printf("  NV12 format (U and V are interleaved buffers) is like :\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tUVUVUVUVUVUVUV\n"
 		 "\t\tUVUVUVUVUVUVUV\n"
	 	 "\t\tUVUVUVUVUVUVUV\n"
 	 	 "\t\tUVUVUVUVUVUVUV\n");

	printf("\n\nThis program captures YUV buffer in YUV422 format for preview buffer, and save as YV16.\n");
	printf("  YV16 format (U and V are planar buffers) is like :\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tYYYYYYYYYYYYYYYYYYYYYYYYYYYY\n"
		 "\t\tUUUUUUUUUUUUUUUUUUUUUUUUUUUU\n"
		 "\t\tUUUUUUUUUUUUUUUUUUUUUUUUUUUU\n"
		 "\t\tVVVVVVVVVVVVVVVVVVVVVVVVVVVV\n"
		 "\t\tVVVVVVVVVVVVVVVVVVVVVVVVVVVV\n");


	printf("\neg: To get one single preview frame of IYUV format\n");
	printf("    > test_yuvcap -b 1 -Y -f 1.yuv -F 0 --tcp\n\n");
	printf("    To get continous preview as .yuv file of YV12 format\n");
	printf("    > test_yuvcap -b 1 -Y -f 1.yuv -F 1 -r 30 --tcp\n\n");
	printf("    To get continous me1 as .yuv file\n");
	printf("    > test_yuvcap -b 0 -m -b 1 -m -f 2.me1 -r 20 --tcp\n\n");
	printf("    To get raw data from RGB sensor input, please enter \n");
	printf("    > test_yuvcap -R -f cap_raw --tcp\n");
}

static int init_param(int argc, char **argv)
{
	int ch, value;
	int option_index = 0;

	opterr = 0;
	while ((ch = getopt_long(argc, argv, short_options, long_options, &option_index)) != -1) {
		switch (ch) {
		case 'b':
			value = atoi(optarg);
			if ((value < IAV_ENCODE_SOURCE_BUFFER_FIRST) ||
				(value >= IAV_ENCODE_SOURCE_BUFFER_LAST)) {
				printf("Invalid preview buffer id : %d.\n", value);
				return -1;
			}
			current_buffer = value;
			break;
		case 'Y':
			VERIFY_BUFFERID(current_buffer);
			capture_select = CAPTURE_PREVIEW_BUFFER;
			yuv_buffer_id |= (1 << current_buffer);
			break;
		case 'm':
			VERIFY_BUFFERID(current_buffer);
			capture_select = CAPTURE_MOTION_BUFFER;
			me1_buffer_id |= (1 << current_buffer);
			break;
		case 'R':
			capture_select = CAPTURE_RAW_BUFFER;
			break;
		case 'f':
			strcpy(filename, optarg);
			break;
		case 'F':
			value = atoi(optarg);
			if ((value != YUV420_IYUV) && (value != YUV420_NV12) &&
				(value != YUV420_YV12)) {
				printf("Invalid output yuv 420 format : %d.\n", value);
				return -1;
			}
			yuv420_format = value;
			break;
		case 't':
			transfer_method = TRANS_METHOD_TCP;
			break;
		case 'u':
			transfer_method = TRANS_METHOD_USB;
			break;
		case 'r':
			value = atoi(optarg);
			if (value < 0 || value > MAX_FRAME_NUM) {
				printf("Cannot capture YUV or ME1 data over %d frames [%d].\n",
					MAX_FRAME_NUM, value);
				return -1;
			}
			frame_count = value;
			break;
		case 'p':
			print_time_stamp = 1;
			break;
		case 'v':
			verbose = 1;
			break;
		default:
			printf("unknown option found: %c\n", ch);
			return -1;
		}
	}

	if (transfer_method == TRANS_METHOD_TCP ||
		transfer_method == TRANS_METHOD_USB)
		default_filename = default_filename_tcp;
	else
		default_filename = default_filename_nfs;

	return 0;
}

static void sigstop(int a)
{
	quit_yuv_stream = 1;
}

static int check_state(void)
{
	int state;
	if (ioctl(fd_iav, IAV_IOC_GET_STATE, &state) < 0) {
        zlog_error(NORMAL_LOG, "IAV_IOC_GET_STATE, errno: %d, %s", errno, strerror(errno));
		exit(2);
	}

	if ((state != IAV_STATE_PREVIEW) && state != IAV_STATE_ENCODING) {
        zlog_error(NORMAL_LOG, "IAV is not in preview / encoding state, cannot get yuv buf!\n");
		return -1;
	}

	return 0;
}
#if 0
/* Prepare a dummy image. */
static void fill_yuv_image(AVPicture *pict,int frame_index,int width, int height)
{
    int x, y, i;
    i = frame_index;
    /* Y */
    for (y = 0; y < height; y++)
        for (x = 0; x < width; x++)
            pict->data[0][y * pict->linesize[0] +x] = x + y + i * 3;
        
    /* Cb and Cr */
    for (y = 0; y < height / 2; y++) 
    {
        for (x = 0; x < width / 2; x++) 
        {
            pict->data[1][y * pict->linesize[1] +x] = 128 + y + i * 2;
            pict->data[2][y * pict->linesize[2] +x] = 64 + x + i * 5;
        }
    }
}
#endif
static AVStream* add_video_stream(AVFormatContext *oc,AVCodec **codec, enum AVCodecID codec_id)
{
    AVCodecContext *c; 
    AVStream *st;     
    /* find the video encoder */
    *codec = avcodec_find_encoder(codec_id);      
    st = avformat_new_stream(oc, *codec);
    c = st->codec;
    avcodec_get_context_defaults3(c, *codec);
    c->codec_id = codec_id;
    c->width = OUTWIDTH;
    c->height = OUTHEIGHT;
    c->gop_size = 10; /* emit one intra frame every ten frames */
    c->max_b_frames = 1; //1
    c->time_base.den = FPS;
    c->time_base.num = 1;
    c->thread_count = 2;
    c->scenechange_threshold = 40;
    c->pix_fmt = AV_PIX_FMT_YUV420P;
    c->max_b_frames = 0; //1
    if(oc->oformat->flags & AVFMT_GLOBALHEADER)
        c->flags|= CODEC_FLAG_GLOBAL_HEADER;
    av_opt_set(c->priv_data, "preset", "ultrafast", 0);
    av_opt_set(c->priv_data, "tune","stillimage,fastdecode,zerolatency",0);
    av_opt_set(c->priv_data, "x264opts","crf=26:vbv-maxrate=728:vbv-bufsize=364:keyint=25",0);
    return st;
}

static int init_x264_encoder()
{
    zlog_debug(DEBUG_LOG, "function start");
    int ret;
    //video encoder init

    avcodec_register_all();
    av_register_all();
    avformat_network_init();

    fmtctx = avformat_alloc_context();
    fmtctx->oformat = av_guess_format("rtp", NULL, NULL);
    if (NULL == fmtctx->oformat)
    {
        zlog_error(NORMAL_LOG, "fmtctx->oformat is %p, get output format fail!", fmtctx->oformat);
        return -1;
    }
    snprintf(fmtctx->filename, sizeof(fmtctx->filename), "rtp://%s:%d", RDIP, RDPORT);
    zlog_info(NORMAL_LOG, "fmtctx->filename:%s", fmtctx->filename);

    if (0 > avio_open(&fmtctx->pb, fmtctx->filename, AVIO_FLAG_WRITE))
    {
        zlog_error(NORMAL_LOG, "avio_open called fail!, error:%d, %s", errno, strerror(errno));
        return -1;
    }
    
    video_st = NULL;
    video_st = add_video_stream(fmtctx, &video_codec, AV_CODEC_ID_H264);

    // OPEN THE CODE
    avcodec_open2(video_st->codec, video_codec, NULL);
    /* Write the stream header, if any. */
    avformat_write_header(fmtctx, NULL);
    
#if 0
    frame = av_frame_alloc();

    frame->format = video_st->codec->pix_fmt;
    frame->width = video_st->codec->width;
    frame->height = video_st->codec->height;

    zlog_info(NORMAL_LOG, "video_st->codec->pix_fmt:%d, video_st->codec->width:%d, video_st->codec->height: %d", video_st->codec->pix_fmt, video_st->codec->width, video_st->codec->height);
    ret = av_image_alloc(frame->data, frame->linesize, video_st->codec->width, video_st->codec->height, video_st->codec->pix_fmt, 32);
    if (ret < 0) {
        zlog_error(NORMAL_LOG, "Could not allocate raw picture buffer");
        return -1;
    }
#endif    

#if 0    
    /* find the mpeg1 video encoder */
    codec = avcodec_find_encoder(AV_CODEC_ID_H264);
    if (!codec) {
        zlog_error(NORMAL_LOG, "Codec not found");
        exit(1);
    }

    codec_context = avcodec_alloc_context3(codec);
    if (!codec_context) {
        zlog_error(NORMAL_LOG, "Could not allocate video codec context");
        exit(1);
    }
    avcodec_get_context_defaults3(codec_context, codec);    /* put sample parameters */
    
    codec_context->bit_rate = 400000;
    /* resolution must be a multiple of two */
    codec_context->width = 720; // 352;
    codec_context->height = 480; // 288;
    /* frames per second */
    codec_context->time_base = (AVRational) {1, 30};
    codec_context->gop_size = 30; /* emit one intra frame every ten frames */
    codec_context->max_b_frames = 1; //1
    //codec_context->pix_fmt = AV_PIX_FMT_YUV422P; //v4l2是这个格式  AV_PIX_FMT_YUV420P;
    //codec_context->pix_fmt = YUV420_IYUV;
    codec_context->pix_fmt = AV_PIX_FMT_YUV420P;
 #if 0   
    //av_opt_set(codec_context->priv_data, "preset", "slow", 0);//ultrafast
    av_opt_set(codec_context->priv_data, "preset", "ultrafast", 0);
    av_opt_set(codec_context->priv_data, "tune", "zerolatency", 0); //ffmpeg
#else
    av_opt_set(codec_context->priv_data, "preset", "ultrafast", 0);
    av_opt_set(codec_context->priv_data, "tune","stillimage,fastdecode,zerolatency",0);
    av_opt_set(codec_context->priv_data, "x264opts","crf=26:vbv-maxrate=728:vbv-bufsize=364:keyint=25",0);
#endif
    /* open it */
    if (avcodec_open2(codec_context, codec, NULL) < 0) {
        zlog_error(NORMAL_LOG, "Could not open codec");
        exit(1);
    }

    frame = av_frame_alloc();
    if (!frame) {
        zlog_error(NORMAL_LOG, "Could not allocate video frame");
        exit(1);
    }
    frame->format = codec_context->pix_fmt;
    frame->width = codec_context->width;
    frame->height = codec_context->height;

    /* the image can be allocated by any means and av_image_alloc() is
    * just the most convenient way if av_malloc() is to be used */
    ret = av_image_alloc(frame->data, frame->linesize, codec_context->width, codec_context->height, codec_context->pix_fmt, 32);
    if (ret < 0) {
        zlog_error(NORMAL_LOG, "Could not allocate raw picture buffer");
        exit(1);
    }
#endif
    create_encoder_pthread(&enc_pid);
    
    zlog_info(NORMAL_LOG, "encoder init complete!");
    return 0;
}

static int destroy_x264_encoder()
{
    zlog_debug(DEBUG_LOG, "function start");
    destroy_encoder_pthread();
    
	fwrite(endcode, 1, sizeof(endcode), f);
	fclose(f);
#if 0    
	/* add sequence end code to have a real mpeg file */
    close(pipe_fd[1]);

    waitpid(ffmpeg_pid, NULL, 0);//wait ffmpeg stop
    
	avcodec_close(codec_context);
	av_free(codec_context);
	av_freep(&frame->data[0]);
	av_frame_free(&frame);
#endif
    //av_frame_free(&frame);
    av_write_trailer(fmtctx);     
    /* Free the streams. */
    unsigned int i = 0;
    for (i = 0; i< fmtctx->nb_streams;i++) 
    {
        av_freep(&fmtctx->streams[i]->codec);
        av_freep(&fmtctx->streams[i]);
    }
    
    if(!(fmtctx->oformat->flags& AVFMT_NOFILE))
        /* Close the output file. */
        avio_close(fmtctx->pb);            
    /*free the stream */     
    zlog_info(NORMAL_LOG, "close stream :%d ", fmtctx->nb_streams);
    //avformat_free_context(fmtctx);
    //av_freep(&frame->data[0]);
	//av_frame_free(&frame);
    zlog_info(NORMAL_LOG, "encoder destroy complete!");
    return 0;
}


int main(int argc, char **argv)
{
	int ret = 0, i;

	//register signal handler for Ctrl+C,  Ctrl+'\'  ,  and "kill" sys cmd
	signal(SIGINT, 	sigstop);
	signal(SIGQUIT,	sigstop);
	signal(SIGTERM,	sigstop);

	if (argc < 2) {
		usage();
		return -1;
	}
    
	if (init_param(argc, argv) < 0) {
		usage();
		return -1;
	}

    init_zlog_config(&yuv_log);

    // open the device
	if ((fd_iav = open("/dev/iav", O_RDWR, 0)) < 0) {
        zlog_error(NORMAL_LOG, "/dev/iav, errno: %d, %s", errno, strerror(errno));
		return -1;
	}
    
    f = fopen(filename, "wb");
    if (!f) {
        zlog_error(NORMAL_LOG, "Could not open %s, errno: %d, %s", filename, errno, strerror(errno));
        exit(1);
    }
    
	if (map_buffer() < 0)
		return -1;

	//check iav state
	if (check_state() < 0)
		return -1;
    

	if (amba_transfer_init(transfer_method) < 0) {
		return -1;
	}

	if (filename[0] == '\0')
		strcpy(filename, default_filename);

	for (i = IAV_ENCODE_SOURCE_BUFFER_FIRST;
		i < IAV_ENCODE_SOURCE_BUFFER_LAST; ++i) {
		fd_yuv[i] = -1;
		fd_me1[i] = -1;
	}

    zlog_info(NORMAL_LOG, "test_yuv");

    open_fifo_file(&wfifo, WRITE_MODE);
    //init x264 encoder
    init_x264_encoder();
    //sleep(10);
    //zlog_info(NORMAL_LOG, "w:%d,h:%d", codec_context->width, codec_context->height);
    
	switch (capture_select) {
	case CAPTURE_PREVIEW_BUFFER:
		capture_yuv(yuv_buffer_id, frame_count);
		break;
	case CAPTURE_MOTION_BUFFER:
		capture_me1(me1_buffer_id, frame_count);
		break;
	case CAPTURE_RAW_BUFFER:
		capture_raw();
		break;
	default:
		zlog_error(NORMAL_LOG, "Invalid capture mode [%d] !", capture_select);
		return -1;
		break;
	}

	if (amba_transfer_deinit(transfer_method) < 0) {
		ret = -1;
	}

    //destroy x264 encoder
    destroy_x264_encoder();
    close_fifo_file(&wfifo);
    destroy_zlog_config(&yuv_log);
    
	return ret;
    
}



