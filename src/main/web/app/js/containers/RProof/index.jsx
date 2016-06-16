import { connect } from 'react-redux'
import Proof from '../../components/Proof'

const mapStateToProps = (state) => (
  {
    lines: [],
    complete: false
  }
)

const mapDispatchToProps = (dispatch) => (
  {

  }
)

const RProof = connect(
  mapStateToProps,
  mapDispatchToProps
)(Proof)

export default RProof

