import { connect } from 'react-redux'
import FileUpload from '../components/FileUpload'
import { uploadProofStructure } from '../actions'

const mapStateToProps = () => ({})

const mapDispatchToProps = (dispatch) => (
  {
    onButtonClick: (file) => dispatch(uploadProofStructure(file))
  }
)

const RProofStructUpload = connect(
  mapStateToProps,
  mapDispatchToProps
)(FileUpload)

export default RProofStructUpload

