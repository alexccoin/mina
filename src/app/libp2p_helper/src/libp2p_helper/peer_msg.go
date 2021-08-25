package main

import (
	"context"
	"fmt"
	"io"

	"codanet"

	capnp "capnproto.org/go/capnp/v3"
	"github.com/go-errors/errors"
	peer "github.com/libp2p/go-libp2p-core/peer"
	peerstore "github.com/libp2p/go-libp2p-core/peerstore"
	ipc "libp2p_ipc"
)

func (app *app) handleAddPeer(seqno uint64, m ipc.Libp2pHelperInterface_AddPeer_Request) *capnp.Message {
	if app.P2p == nil {
		return mkRpcRespError(seqno, needsConfigure())
	}

	maddr, err := m.Multiaddr()
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}
	maRepr, err := maddr.Representation()
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}
	info, err := addrInfoOfString(maRepr)
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}

	app.AddedPeers = append(app.AddedPeers, *info)
	app.P2p.GatingState.TrustedPeers.Add(info.ID)

	if app.Bootstrapper != nil {
		app.Bootstrapper.Close()
	}

	app.P2p.Logger.Info("addPeer Trying to connect to: ", info)

	if m.IsSeed() {
		app.P2p.Seeds = append(app.P2p.Seeds, *info)
	}

	err = app.P2p.Host.Connect(app.Ctx, *info)
	if err != nil {
		return mkRpcRespError(seqno, badp2p(err))
	}

	return mkRpcRespSuccess(seqno, func(m *ipc.Libp2pHelperInterface_RpcResponseSuccess) {
		_, err := m.NewAddPeer()
		panicOnErr(err)
	})
}

func (app *app) handleFindPeer(seqno uint64, m ipc.Libp2pHelperInterface_FindPeer_Request) *capnp.Message {
	pid, err := m.PeerId()
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}
	peerId, err := pid.Id()
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}
	id, err := peer.Decode(peerId)
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}

	peerInfo, err := findPeerInfo(app, id)

	if err != nil {
		return mkRpcRespError(seqno, badp2p(err))
	}

	return mkRpcRespSuccess(seqno, func(m *ipc.Libp2pHelperInterface_RpcResponseSuccess) {
		r, err := m.NewFindPeer()
		panicOnErr(err)
		res, err := r.NewResult()
		panicOnErr(err)
		setPeerInfo(res, peerInfo)
	})
}

func (app *app) handleGetPeerNodeStatus(seqno uint64, m ipc.Libp2pHelperInterface_GetPeerNodeStatus_Request) *capnp.Message {
	ctx, _ := context.WithTimeout(app.Ctx, codanet.NodeStatusTimeout)
	pma, err := m.Peer()
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}
	pmaRepr, err := pma.Representation()
	if err != nil {
		return mkRpcRespError(seqno, badRPC(err))
	}
	addrInfo, err := addrInfoOfString(pmaRepr)
	if err != nil {
		return mkRpcRespError(seqno, err)
	}
	app.P2p.Host.Peerstore().AddAddrs(addrInfo.ID, addrInfo.Addrs, peerstore.ConnectedAddrTTL)

	// Open a "get node status" stream on m.PeerID,
	// block until you can read the response, return that.
	s, err := app.P2p.Host.NewStream(ctx, addrInfo.ID, codanet.NodeStatusProtocolID)
	if err != nil {
		app.P2p.Logger.Error("failed to open stream: ", err)
		return mkRpcRespError(seqno, err)
	}

	defer func() {
		_ = s.Close()
	}()

	errCh := make(chan error)
	responseCh := make(chan []byte)

	go func() {
		// 1 megabyte
		size := 1048576

		data := make([]byte, size)
		n, err := s.Read(data)
		// TODO will the whole status be read or we can "accidentally" read only
		// part of it?
		if err != nil && err != io.EOF {
			app.P2p.Logger.Errorf("failed to decode node status data: err=%s", err)
			errCh <- err
			return
		}

		if n == size && err == nil {
			errCh <- fmt.Errorf("node status data was greater than %d bytes", size)
			return
		}

		responseCh <- data[:n]
	}()

	select {
	case <-ctx.Done():
		s.Reset()
		err := errors.New("timed out requesting node status data from peer")
		return mkRpcRespError(seqno, err)
	case err := <-errCh:
		return mkRpcRespError(seqno, err)
	case response := <-responseCh:
		return mkRpcRespSuccess(seqno, func(m *ipc.Libp2pHelperInterface_RpcResponseSuccess) {
			r, err := m.NewGetPeerNodeStatus()
			panicOnErr(err)
			r.SetResult(response)
		})
	}
}

func (app *app) handleListPeers(seqno uint64, m ipc.Libp2pHelperInterface_ListPeers_Request) *capnp.Message {
	if app.P2p == nil {
		return mkRpcRespError(seqno, needsConfigure())
	}

	connsHere := app.P2p.Host.Network().Conns()

	peerInfos := make([]codaPeerInfo, 0, len(connsHere))

	for _, conn := range connsHere {
		maybePeer, err := parseMultiaddrWithID(conn.RemoteMultiaddr(), conn.RemotePeer())
		if err != nil {
			app.P2p.Logger.Warning("skipping maddr ", conn.RemoteMultiaddr().String(), " because it failed to parse: ", err.Error())
			continue
		}
		peerInfos = append(peerInfos, *maybePeer)
	}

	return mkRpcRespSuccess(seqno, func(m *ipc.Libp2pHelperInterface_RpcResponseSuccess) {
		r, err := m.NewListPeers()
		panicOnErr(err)
		lst, err := r.NewResult(int32(len(peerInfos)))
		panicOnErr(err)
		setPeerInfoList(lst, peerInfos)
	})
}